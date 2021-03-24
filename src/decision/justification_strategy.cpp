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
  JustifyInfo* ji;
  JustifyNode next;
  SatValue nextVal;
  context::CDInsertHashMap<Node, SatValue, NodeHashFunction>::const_iterator
      jit;
  while (!d_current.get().isNull())
  {
    // get the current justify info, which should be ready
    Assert(d_stackSizeValid.get() > 0);
    Assert(d_stack.size() >= d_stackSizeValid.get());
    ji = d_stack[d_stackSizeValid.get() - 1].get();
    // get the next justify node
    next = getNextJustifyNode(ji, SAT_VALUE_UNKNOWN);
    do
    {
      // must have requested a child
      Assert(!next.first.isNull());
      Assert(next.first.getKind() != NOT);
      Assert(next.second != SAT_VALUE_UNKNOWN);
      jit = d_justified.find(next.first);
      // have we processed this node yet?
      if (jit == d_justified.end())
      {
        if (isTheoryAtom(next.first))
        {
          // should be assigned a literal
          Assert(hasSatLiteral(next.first));
          SatLiteral asl = getSatLiteral(next.first);
          // maybe it has a SAT value already?
          nextVal = d_satSolver->value(asl);
          if (nextVal == SAT_VALUE_UNKNOWN)
          {
            // (1) atom with unassigned value, return it, possibly inverted
            return next.second == SAT_VALUE_FALSE ? ~asl : asl;
          }
          // otherwise, we already have the correct or incorrect value below
        }
        else
        {
          // (2) unprocessed non-atom, push to the stack
          // push the child to the stack
          pushToStack(next.first, next.second);
          continue;
        }
      }
      else
      {
        nextVal = jit->second;
      }
      Assert(nextVal != SAT_VALUE_UNKNOWN);
      // check whether we have the value we wanted
      bool lastChildSuccess = (nextVal == next.second);
      // we now get the next justify node again, if it can be found
      // (3) if we already have the desired value, we pop recursively until a
      // "hard" node, or reach the top of the current assertion, or 
      // (4) if we already have the wrong value, we continue if we are an
      // "easy" node.
      do
      {
        next = getNextJustifyNode(ji, lastChildSuccess);
        // if the current node is finished, we pop the stack
        if (!next.first.isNull())
        {
          popStack();
          ji = d_stack[d_stackSizeValid.get() - 1].get();
        }
      } while (!next.first.isNull() && d_stackSizeValid.get() > 0);
    } while (d_stackSizeValid.get() > 0);

    // we did not find a decision for current, refresh current assertion
    refreshCurrentAssertion();
  }

  // we exhausted all assertions
  return undefSatLiteral;
}

JustifyNode JustificationStrategy::getNextJustifyNode(JustifyInfo * ji, bool lastChildSuccess)
{
  JustifyNode curr = ji->getNode();
  Kind ck = curr.first.getKind();
  Assert(ck != NOT);
  Assert(!isTheoryAtom(curr.first));
  
  if (lastChildSuccess)
  {
    // TODO: we return null if we are done with the current node
  }
  JustifyNode nextChild;
  // the current node should be a non-negated non-theory literal, due to our
  // invariants of what is pushed onto the stack
  // get the next index to process, and construct the next child request
  size_t i = ji->getNextChildIndex();
  Assert(i < curr.first.getNumChildren());
  nextChild.first = curr.first[i];
  nextChild.second = curr.second;
  // determine if we flip polarity?
  if (ck == AND || ck == OR || ck == IMPLIES)
  {
    
  }
  else if (ck == ITE)
  {
  }
  else if (ck == XOR || ck == EQUAL)
  {
    Assert(curr.first[0].getType().isBoolean());
  }
  else
  {
    // curr should not be an atom
    Assert(false);
  }
  // flip polarity if a NOT node
  if (nextChild.first.getKind() == NOT)
  {
    nextChild.first = nextChild.first[0];
    nextChild.second = invertValue(nextChild.second);
  }
  return nextChild;
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

bool JustificationStrategy::hasSatLiteral(TNode n)
{
  return d_cnfStream->hasLiteral(n);
}

SatLiteral JustificationStrategy::getSatLiteral(TNode n)
{
  return d_cnfStream->getLiteral(n);
}

SatValue JustificationStrategy::getSatValue(SatLiteral l)
{
  return d_satSolver->value(l);
}

SatValue JustificationStrategy::getSatValue(TNode n)
{
  return getSatValue(getSatLiteral(n));
}

Node JustificationStrategy::getNode(SatLiteral l)
{
  return d_cnfStream->getNode(l);
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
      // if not already justified, we reset the stack and push it
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
  Assert(catom.getKind() != NOT);
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
