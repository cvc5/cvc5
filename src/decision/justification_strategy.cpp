/*********************                                                        */
/*! \file justification_strategy.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Justification strategy
 **/

#include "decision/justification_strategy.h"

using namespace CVC4::kind;
using namespace CVC4::prop;

namespace CVC4 {

JustificationStrategy::JustificationStrategy(context::Context* c,
                                             context::UserContext* u)
    : d_context(c),
      d_cnfStream(nullptr),
      d_satSolver(nullptr),
      d_assertions(u, c),        // assertions are user-context dependent
      d_skolemAssertions(c, c),  // skolem assertions are SAT-context dependent
      d_current(c),
      d_justified(c),
      d_stack(c),
      d_stackSizeValid(c, 0)
{
}

void JustificationStrategy::finishInit(CDCLTSatSolverInterface* ss,
                                       CnfStream* cs)
{
  d_satSolver = ss;
  d_cnfStream = cs;
}

SatLiteral JustificationStrategy::getNext(bool& stopSearch)
{
  // ensure we have an assertion, this could perhaps be an Assert?
  refreshCurrentAssertion();
  // temporary information in the loop below
  JustifyInfo* ji;
  JustifyNode next;
  SatValue lastChildVal = SAT_VALUE_UNKNOWN;
  // while we are trying to satisfy assertions
  while (!d_current.get().isNull())
  {
    // We get the next justify node, if it can be found.
    do
    {
      // get the current justify info, which should be ready
      Assert(d_stackSizeValid.get() > 0);
      Assert(d_stack.size() >= d_stackSizeValid.get());
      ji = d_stack[d_stackSizeValid.get() - 1].get();
      // get the next child to process from the current justification info
      next = getNextJustifyNode(ji, lastChildVal);
      // if the current node is finished, we pop the stack
      if (!next.first.isNull())
      {
        popStack();
      }
    } while (!next.first.isNull() && d_stackSizeValid.get() > 0);

    if (d_stackSizeValid.get() == 0)
    {
      // we did not find a next node for current, refresh current assertion
      refreshCurrentAssertion();
    }
    else
    {
      // must have requested a child
      Assert(!next.first.isNull());
      Assert(next.second != SAT_VALUE_UNKNOWN);
      // Look up whether next.first already has a value
      lastChildVal = lookupValue(next.first);
      // have we processed the next node yet?
      if (lastChildVal == SAT_VALUE_UNKNOWN)
      {
        if (isTheoryLiteral(next.first))
        {
          // should be assigned a literal
          Assert(d_cnfStream->hasLiteral(next.first));
          // maybe it has a SAT value already?
          SatLiteral nsl = d_cnfStream->getLiteral(next.first);
          // (1) atom with unassigned value, return it, possibly inverted
          return next.second == SAT_VALUE_FALSE ? ~nsl : nsl;
        }
        else
        {
          // (2) unprocessed non-atom, push to the stack
          // push the child to the stack
          pushToStack(next.first, next.second);
          // we have yet to process children for the new node
          continue;
        }
      }
      // (3) otherwise, formula that already has a value
    }
  }
  // we exhausted all assertions
  return undefSatLiteral;
}

JustifyNode JustificationStrategy::getNextJustifyNode(
    JustifyInfo* ji, prop::SatValue& lastChildVal)
{
  JustifyNode jc = ji->getNode();
  Assert(!jc.first.isNull());
  Assert(jc.second != SAT_VALUE_UNKNOWN);
  // extract the non-negated formula from jc
  bool currPol = jc.first.getKind() != NOT;
  TNode curr = currPol ? jc.first : jc.first[0];
  Kind ck = curr.getKind();
  Assert(ck != NOT);
  // the current node should be a non-theory literal, due to our
  // invariants of what is pushed onto the stack
  Assert(!isTheoryAtom(curr));
  // get the next child index to process
  size_t i = ji->getNextChildIndex();
  if (lastChildVal != SAT_VALUE_UNKNOWN)
  {
    Assert(i != 0);
    // we just computed the value of the (i-1)^th child, compute if we have a
    // value now
    SatValue value = SAT_VALUE_UNKNOWN;
    if (ck == AND || ck == OR || ck == IMPLIES)
    {
      if ((ck == AND) == (lastChildVal == SAT_VALUE_FALSE))
      {
        // forcing case
        value = lastChildVal;
      }
      else if (i == curr.getNumChildren())
      {
        // exhausted case
        value = invertValue(lastChildVal);
      }
      // otherwise, no forced value
    }
    else if (ck == ITE)
    {
      if (i == 1)
      {
        // take the else branch if the condition was false
        if (lastChildVal == SAT_VALUE_FALSE)
        {
          i = ji->getNextChildIndex();
        }
      }
      else
      {
        // return the branch value
        value = lastChildVal;
      }
    }
    else
    {
      Assert(ck == XOR || ck == EQUAL);
      Assert(i == 1);
      // no value yet
    }
    // we return null if we are done with the current node
    if (value != SAT_VALUE_UNKNOWN)
    {
      // add to justify if so
      d_justified.insert(curr, value);
      // update the last child value, which will be used by the parent of this,
      // if it exists
      lastChildVal = value;
      return JustifyNode(TNode::null(), SAT_VALUE_UNKNOWN);
    }
  }
  JustifyNode nextChild;
  // The next child should be in the range of curr. Otherwise, we did not
  // recognize when its value could be inferred above.
  Assert(i < curr.getNumChildren());
  nextChild.first = curr[i];
  // determine the value of the next child request
  SatValue desiredVal = currPol ? jc.second : invertValue(jc.second);
  // TODO: lookahead

  // determine if already justified
  if (ck == AND || ck == OR)
  {
    nextChild.second = desiredVal;
  }
  else if (ck == IMPLIES)
  {
    nextChild.second = (i == 0) ? invertValue(desiredVal) : desiredVal;
  }
  else if (ck == ITE)
  {
    nextChild.second = (i == 0) ? SAT_VALUE_TRUE : desiredVal;
  }
  else if (ck == XOR)
  {
    nextChild.second = (i == 0) ? SAT_VALUE_TRUE : invertValue(lastChildVal);
  }
  else if (ck == EQUAL)
  {
    nextChild.second = (i == 0) ? SAT_VALUE_TRUE : lastChildVal;
  }
  else
  {
    // curr should not be an atom
    Assert(false);
  }
  return nextChild;
}

prop::SatValue JustificationStrategy::lookupValue(TNode n)
{
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  Assert(atom.getKind() != NOT);
  // check if we have already determined the value
  // notice that d_justified may contain nodes that are not assigned SAT values,
  // since this class infers when the value of nodes can be determined.
  context::CDInsertHashMap<Node, SatValue, NodeHashFunction>::const_iterator
      jit = d_justified.find(atom);
  if (jit != d_justified.end())
  {
    return pol ? jit->second : invertValue(jit->second);
  }
  // TODO: for simplicity, should we just lookup values for non-theory atoms
  // too?
  if (isTheoryAtom(atom))
  {
    SatLiteral nsl = d_cnfStream->getLiteral(atom);
    prop::SatValue val = d_satSolver->value(nsl);
    if (val != SAT_VALUE_UNKNOWN)
    {
      d_justified.insert(atom, val);
    }
    return pol ? val : invertValue(val);
  }
  return SAT_VALUE_UNKNOWN;
}

bool JustificationStrategy::isDone() { return refreshCurrentAssertion(); }

void JustificationStrategy::addAssertion(TNode assertion)
{
  // we skip (top-level) theory literals, since these will always be propagated
  if (!isTheoryLiteral(assertion))
  {
    d_assertions.addAssertion(assertion);
  }
}

void JustificationStrategy::notifyRelevantSkolemAssertion(TNode lem)
{
  // similar to above, we skip theory literals
  if (!isTheoryLiteral(lem))
  {
    d_skolemAssertions.addAssertion(lem);
  }
}

bool JustificationStrategy::refreshCurrentAssertion()
{
  // if we already have a current assertion, nothing to be done
  if (!d_current.get().isNull())
  {
    return true;
  }
  // use main assertions first
  if (refreshCurrentAssertionFromList(d_assertions))
  {
    return true;
  }
  // if satisfied all main assertions, use the skolem assertions, which may
  // fail
  return refreshCurrentAssertionFromList(d_skolemAssertions);
}

bool JustificationStrategy::refreshCurrentAssertionFromList(AssertionList& al)
{
  TNode curr = al.getNextAssertion();
  while (!curr.isNull())
  {
    // we never add theory literals to our assertions lists
    Assert(!isTheoryLiteral(curr));
    if (d_justified.find(curr) == d_justified.end())
    {
      // if not already justified, we reset the stack and push to it
      d_current = curr;
      d_stackSizeValid = 0;
      pushToStack(curr, SAT_VALUE_TRUE);
      return true;
    }
    curr = al.getNextAssertion();
  }
  return false;
}

void JustificationStrategy::pushToStack(TNode n, SatValue desiredVal)
{
  // set up the initial info: we want to set the atom of c to its polarity
  bool pol = n.getKind() != NOT;
  TNode atom = pol ? n : n[0];
  // double negations should always be eliminated
  Assert(atom.getKind() != NOT);
  JustifyInfo* ji = getOrAllocJustifyInfo(d_stackSizeValid.get());
  ji->set(atom, pol ? desiredVal : invertValue(desiredVal));
  d_stackSizeValid = d_stackSizeValid + 1;
}

void JustificationStrategy::popStack()
{
  Assert(d_stackSizeValid.get() > 0);
  d_stackSizeValid = d_stackSizeValid - 1;
}

JustifyInfo* JustificationStrategy::getOrAllocJustifyInfo(size_t i)
{
  // don't request stack beyond the bound
  Assert(i <= d_stack.size());
  if (i == d_stack.size())
  {
    d_stack.push_back(std::make_shared<JustifyInfo>(d_context));
  }
  return d_stack[i].get();
}

bool JustificationStrategy::isTheoryLiteral(TNode n)
{
  return isTheoryAtom(n.getKind() == NOT ? n[0] : n);
}

bool JustificationStrategy::isTheoryAtom(TNode n)
{
  Kind k = n.getKind();
  Assert(k != NOT);
  return k != AND && k != OR && k != IMPLIES && k != ITE && k != XOR
         && (k != EQUAL || !n[0].getType().isBoolean());
}

}  // namespace CVC4
