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

const char* toString(DecisionStatus s)
{
  switch (s)
  {
    case DecisionStatus::INACTIVE: return "INACTIVE";
    case DecisionStatus::NO_DECISION: return "NO_DECISION";
    case DecisionStatus::DECISION: return "DECISION";
    case DecisionStatus::BACKTRACK: return "BACKTRACK";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, DecisionStatus s)
{
  out << toString(s);
  return out;
}

JustificationStrategy::JustificationStrategy(context::Context* c,
                                             context::UserContext* u,
                                             prop::SkolemDefManager* skdm)
    : d_context(c),
      d_cnfStream(nullptr),
      d_satSolver(nullptr),
      d_skdm(skdm),
      d_assertions(u, c),        // assertions are user-context dependent
      d_skolemAssertions(c, c),  // skolem assertions are SAT-context dependent
      d_justified(c),
      d_stack(c),
      d_lastDecisionLit(c),
      d_currStatus(DecisionStatus::INACTIVE),
      d_currUnderStatusIndex(0),
      d_useRlvOrder(options::jhNewRlvOrder()),
      d_jhSkMode(options::jhNewSkolemMode()),
      d_jhSkRlvMode(options::jhNewSkolemRlvMode())
{
}

void JustificationStrategy::finishInit(CDCLTSatSolverInterface* ss,
                                       CnfStream* cs)
{
  d_satSolver = ss;
  d_cnfStream = cs;
}

void JustificationStrategy::presolve()
{
  // TODO
}

SatLiteral JustificationStrategy::getNext(bool& stopSearch)
{
  // ensure we have an assertion
  if (!refreshCurrentAssertion())
  {
    Trace("jh-process") << "getNext, already finished" << std::endl;
    stopSearch = true;
    return undefSatLiteral;
  }
  Assert(d_stack.hasCurrentAssertion());
  // temporary information in the loop below
  JustifyInfo* ji;
  JustifyNode next;
  // we start with the value implied by the last decision, if it exists
  SatValue lastChildVal = SAT_VALUE_UNKNOWN;  // d_lastDecisionValue.get();
  Trace("jh-process") << "getNext" << std::endl;
  // If we had just sent a decision, then we lookup its value here. This may
  // correspond to a context where the decision was carried out, or
  // alternatively it may correspond to a case where we have backtracked and
  // propagated that literal with opposite polarity. Thus, we do not assume we
  // know the value of d_lastDecisionLit and look it up again here. The value
  // of lastChildVal will be used to update the justify info in the current
  // stack below.
  if (!d_lastDecisionLit.get().isNull())
  {
    Trace("jh-process") << "last decision = " << d_lastDecisionLit.get()
                        << std::endl;
    lastChildVal = lookupValue(d_lastDecisionLit.get());
    if (lastChildVal == SAT_VALUE_UNKNOWN)
    {
      // if the value is now unknown, we must reprocess the child
      ji = d_stack.getCurrent();
      ji->revertChildIndex();
    }
  }
  d_lastDecisionLit = TNode::null();
  // while we are trying to satisfy assertions
  do
  {
    Assert(d_stack.getCurrent() != nullptr);
    // We get the next justify node, if it can be found.
    do
    {
      // get the current justify info, which should be ready
      ji = d_stack.getCurrent();
      if (ji == nullptr)
      {
        break;
      }
      // get the next child to process from the current justification info
      // based on the fact that its last child processed had value lastChildVal.
      next = getNextJustifyNode(ji, lastChildVal);
      // if the current node is finished, we pop the stack
      if (next.first.isNull())
      {
        d_stack.popStack();
      }
    } while (next.first.isNull());

    if (ji == nullptr)
    {
      // assertion should be true?
      // AlwaysAssert(lastChildVal == SAT_VALUE_TRUE) << "Previous assertion "
      // << d_current.get() << " had value " << lastChildVal;
      if (!d_currUnderStatus.isNull())
      {
        // notify status if we are watching it
        notifyStatus(d_currUnderStatusIndex, d_currStatus);
      }
      // we did not find a next node for current, refresh current assertion
      d_stack.clear();
      refreshCurrentAssertion();
      lastChildVal = SAT_VALUE_UNKNOWN;
      Trace("jh-process") << "...exhausted assertion, now "
                          << d_stack.getCurrentAssertion() << std::endl;
    }
    else
    {
      // must have requested a next child to justify
      Assert(!next.first.isNull());
      Assert(next.second != SAT_VALUE_UNKNOWN);
      // Look up whether the next child already has a value
      lastChildVal = lookupValue(next.first);
      if (lastChildVal == SAT_VALUE_UNKNOWN)
      {
        bool nextPol = next.first.getKind() != kind::NOT;
        TNode nextAtom = nextPol ? next.first : next.first[0];
        if (isTheoryAtom(nextAtom))
        {
          // should be assigned a literal
          Assert(d_cnfStream->hasLiteral(nextAtom));
          // get the SAT literal
          SatLiteral nsl = d_cnfStream->getLiteral(nextAtom);
          // flip if the atom was negated
          // store the last decision value here, which will be used at the
          // starting value on the next call to this method
          lastChildVal = nextPol ? next.second : invertValue(next.second);
          // (1) atom with unassigned value, return it as the decision, possibly
          // inverted
          Trace("jh-process")
              << "...return " << nextAtom << " " << lastChildVal << std::endl;
          // Note that the last child of the current node we looked at does
          // *not* yet have a value. Although we are returning it as a decision,
          // we cannot set its value in d_justified, because we have yet to
          // push a decision level. Thus, we remember the literal we decided
          // on. The value of d_lastDecisionLit will be processed at the
          // beginning of the next call to getNext above.
          d_lastDecisionLit = next.first;
          // update the decision
          if (d_currStatus == DecisionStatus::NO_DECISION)
          {
            d_currStatus = DecisionStatus::DECISION;
          }
          return lastChildVal == SAT_VALUE_FALSE ? ~nsl : nsl;
        }
        else
        {
          // TODO: if the internal node has been assigned, what do we do?
          // (2) unprocessed non-atom, push to the stack
          d_stack.pushToStack(next.first, next.second);
          d_stats.d_maxStackSize.maxAssign(d_stack.size());
          // we have yet to process children for the next node, so lastChildVal
          // remains set to SAT_VALUE_UNKNOWN.
        }
      }
      else
      {
        Trace("jh-debug") << "in main loop, " << next.first << " has value "
                          << lastChildVal << std::endl;
      }
      // (3) otherwise, next already has a value lastChildVal which will be
      // processed in the next iteration of the loop.
    }
  } while (d_stack.hasCurrentAssertion());
  // we exhausted all assertions
  Trace("jh-process") << "...exhausted all assertions" << std::endl;
  stopSearch = true;
  return undefSatLiteral;
}

JustifyNode JustificationStrategy::getNextJustifyNode(
    JustifyInfo* ji, prop::SatValue& lastChildVal)
{
  // get the node we are trying to justify and its desired value
  JustifyNode jc = ji->getNode();
  Assert(!jc.first.isNull());
  Assert(jc.second != SAT_VALUE_UNKNOWN);
  // extract the non-negated formula we are trying to justify
  bool currPol = jc.first.getKind() != NOT;
  TNode curr = currPol ? jc.first : jc.first[0];
  Kind ck = curr.getKind();
  // the current node should be a non-theory literal and not have double
  // negation, due to our invariants of what is pushed onto the stack
  Assert(!isTheoryAtom(curr));
  Assert(ck != NOT);
  // get the next child index to process
  size_t i = ji->getNextChildIndex();
  Trace("jh-debug") << "getNextJustifyNode " << curr << " / " << currPol
                    << ", index = " << i
                    << ", last child value = " << lastChildVal << std::endl;
  // if i>0, we just computed the value of the (i-1)^th child
  // doesn't hold for backtracking?
  // Assert(i == 0 || lastChildVal != SAT_VALUE_UNKNOWN)
  //    << "in getNextJustifyNode, last child has no value";
  // if i=0, we shouldn't have a last child value
  Assert(i > 0 || lastChildVal == SAT_VALUE_UNKNOWN)
      << "in getNextJustifyNode, value given for non-existent last child";
  // In the following, we determine if we have a value and set value if so.
  // If not, we set desiredValue for the value of the next value to justify.
  // One of these two values should always be set below.
  SatValue value = SAT_VALUE_UNKNOWN;
  SatValue desiredVal = SAT_VALUE_UNKNOWN;
  // we are trying to make the value of curr equal to currDesiredVal
  SatValue currDesiredVal = currPol ? jc.second : invertValue(jc.second);
  if (ck == AND || ck == OR)
  {
    if (i == 0)
    {
      // Maybe expensive, so only do this for i==0?
      if ((ck == AND) == (currDesiredVal == SAT_VALUE_FALSE))
      {
        // lookahead to determine if already satisfied
        for (const Node& c : curr)
        {
          if (lookupValue(c) == currDesiredVal)
          {
            Trace("jh-debug") << "already forcing child " << c << std::endl;
            value = currDesiredVal;
            break;
          }
        }
      }
      desiredVal = currDesiredVal;
    }
    else if ((ck == AND) == (lastChildVal == SAT_VALUE_FALSE)
             || i == curr.getNumChildren())
    {
      Trace("jh-debug") << "current is forcing child" << std::endl;
      // forcing or exhausted case
      value = lastChildVal;
    }
    else
    {
      // otherwise, no forced value, value of child should match the parent
      desiredVal = currDesiredVal;
    }
  }
  else if (ck == IMPLIES)
  {
    if (i == 0)
    {
      // lookahead to second child to determine if value already forced
      if (lookupValue(curr[1]) == SAT_VALUE_TRUE)
      {
        value = SAT_VALUE_TRUE;
      }
      else
      {
        // otherwise, we request the opposite of what parent wants
        desiredVal = invertValue(currDesiredVal);
      }
    }
    else if (i == 1)
    {
      // forcing case
      if (lastChildVal == SAT_VALUE_FALSE)
      {
        value = SAT_VALUE_TRUE;
      }
      else
      {
        desiredVal = currDesiredVal;
      }
    }
    else
    {
      // exhausted case
      value = lastChildVal;
    }
  }
  else if (ck == ITE)
  {
    if (i == 0)
    {
      // lookahead on branches
      SatValue val1 = lookupValue(curr[1]);
      SatValue val2 = lookupValue(curr[2]);
      if (val1 == val2)
      {
        // branches have no difference, value is that of branches, which may
        // be unknown
        value = val1;
      }
      // if first branch is already wrong or second branch is already correct,
      // try to make condition false. Note that we arbitrarily choose true here
      // if both children are unknown
      desiredVal =
          (val1 == invertValue(currDesiredVal) || val2 == currDesiredVal)
              ? SAT_VALUE_FALSE
              : SAT_VALUE_TRUE;
    }
    else if (i == 1)
    {
      // we just computed the value of the condition, check if the condition
      // was false
      if (lastChildVal == SAT_VALUE_FALSE)
      {
        // this increments to the else branch
        i = ji->getNextChildIndex();
      }
      // make the branch equal to the desired value
      desiredVal = currDesiredVal;
    }
    else
    {
      // return the branch value
      value = lastChildVal;
    }
  }
  else if (ck == XOR || ck == EQUAL)
  {
    Assert(curr[0].getType().isBoolean());
    if (i == 0)
    {
      // check if the rhs forces a value
      SatValue val1 = lookupValue(curr[1]);
      if (val1 == SAT_VALUE_UNKNOWN)
      {
        // not forced, arbitrarily choose true
        desiredVal = SAT_VALUE_TRUE;
      }
      else
      {
        desiredVal = ((ck == EQUAL) == (currDesiredVal == SAT_VALUE_TRUE))
                         ? val1
                         : invertValue(val1);
      }
    }
    else if (i == 1)
    {
      desiredVal = ((ck == EQUAL) == (currDesiredVal == SAT_VALUE_TRUE))
                       ? lastChildVal
                       : invertValue(lastChildVal);
    }
    else
    {
      // recompute the value of the first child
      SatValue val0 = lookupValue(curr[0]);
      Assert(val0 != SAT_VALUE_UNKNOWN);
      // compute the value
      value = ((val0 == lastChildVal) == (ck == EQUAL)) ? SAT_VALUE_TRUE
                                                        : SAT_VALUE_FALSE;
    }
  }
  else
  {
    // curr should not be an atom
    Assert(false);
  }
  // we return null if we have determined the value of the current node
  if (value != SAT_VALUE_UNKNOWN)
  {
    // add to justify if so
    d_justified.insert(curr, value);
    // update the last child value, which will be used by the parent of the
    // current node, if it exists.
    lastChildVal = currPol ? value : invertValue(value);
    Trace("jh-debug") << "getJustifyNode: return null with value "
                      << lastChildVal << std::endl;
    // return null, indicating there is nothing left to do for current
    return JustifyNode(TNode::null(), SAT_VALUE_UNKNOWN);
  }
  Trace("jh-debug") << "getJustifyNode: return " << curr[i]
                    << " with desired value " << desiredVal << std::endl;
  // The next child should be a valid argument in curr. Otherwise, we did not
  // recognize when its value could be inferred above.
  Assert(i < curr.getNumChildren());
  // should set a desired value
  Assert(desiredVal != SAT_VALUE_UNKNOWN);
  // return the justify node
  return JustifyNode(curr[i], desiredVal);
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
  // too? Notice that looking up values for non-theory atoms may lead to
  // an incomplete strategy where a formula is asserted but not justified
  // via its theory literal subterms?
  if (isTheoryAtom(atom))
  {
    SatLiteral nsl = d_cnfStream->getLiteral(atom);
    prop::SatValue val = d_satSolver->value(nsl);
    if (val != SAT_VALUE_UNKNOWN)
    {
      d_justified.insert(atom, val);
      return pol ? val : invertValue(val);
    }
  }
  return SAT_VALUE_UNKNOWN;
}

bool JustificationStrategy::isDone() { return !refreshCurrentAssertion(); }

void JustificationStrategy::addAssertion(TNode assertion)
{
  insertToAssertionList(assertion, false);
}

void JustificationStrategy::notifyRelevantSkolemAssertion(TNode lem)
{
  insertToAssertionList(lem, true);
}

void JustificationStrategy::insertToAssertionList(TNode n, bool useSkolemList)
{
  AssertionList& al = useSkolemList ? d_skolemAssertions : d_assertions;
  // always miniscope AND immediately
  std::vector<TNode> toProcess;
  size_t index = 0;
  toProcess.push_back(n);
  do
  {
    TNode curr = toProcess[index];
    bool pol = curr.getKind() != NOT;
    TNode currAtom = pol ? curr : curr[0];
    index++;
    Kind k = currAtom.getKind();
    if (k == AND && pol)
    {
      toProcess.insert(toProcess.begin() + index, curr.begin(), curr.end());
    }
    else if (k == OR && !pol)
    {
      std::vector<Node> negc;
      for (TNode c : currAtom)
      {
        negc.push_back(c.negate());
      }
      toProcess.insert(toProcess.begin() + index, negc.begin(), negc.end());
    }
    else if (!isTheoryAtom(currAtom))
    {
      al.addAssertion(curr);
      // take stats
      if (useSkolemList)
      {
        d_stats.d_maxSkolemDefsSize.maxAssign(al.size());
      }
      else
      {
        d_stats.d_maxAssertionsSize.maxAssign(al.size());
      }
    }
    else
    {
      // we skip (top-level) theory literals, since these are always propagated
      // TODO: skolem definitions that are always relevant should be added to
      // assertions, for uniformity
    }
  } while (index < toProcess.size());
}

bool JustificationStrategy::refreshCurrentAssertion()
{
  // if we already have a current assertion, nothing to be done
  TNode curr = d_stack.getCurrentAssertion();
  if (!curr.isNull())
  {
    if (curr != d_currUnderStatus && !d_currUnderStatus.isNull())
    {
      notifyStatus(d_currUnderStatusIndex, DecisionStatus::BACKTRACK);
      // we've backtracked to another assertion which may be partially
      // processed. don't track its status?
      d_currUnderStatus = Node::null();
      d_currStatus = DecisionStatus::INACTIVE;
    }
    return true;
  }
  bool skFirst = (d_jhSkMode != options::JutificationSkolemMode::LAST);
  // use main assertions first
  if (refreshCurrentAssertionFromList(skFirst))
  {
    return true;
  }
  // if satisfied all main assertions, use the skolem assertions, which may
  // fail
  return refreshCurrentAssertionFromList(!skFirst);
}

bool JustificationStrategy::refreshCurrentAssertionFromList(bool useSkolemList)
{
  AssertionList& al = useSkolemList ? d_skolemAssertions : d_assertions;
  bool doWatchStatus = true;
  if (useSkolemList)
  {
    doWatchStatus = false;
    d_currUnderStatus = Node::null();
    d_currStatus = DecisionStatus::INACTIVE;
  }
  size_t fromIndex;
  TNode curr = al.getNextAssertion(fromIndex);
  SatValue currValue;
  while (!curr.isNull())
  {
    // we never add theory literals to our assertions lists
    Assert(!isTheoryLiteral(curr));
    currValue = lookupValue(curr);
    if (currValue == SAT_VALUE_UNKNOWN)
    {
      // if not already justified, we reset the stack and push to it
      d_stack.reset(curr);
      d_lastDecisionLit = TNode::null();
      // for activity
      if (doWatchStatus)
      {
        // initially, mark that we have not found a decision in this
        d_currUnderStatus = d_stack.getCurrentAssertion();
        d_currUnderStatusIndex = fromIndex;
        d_currStatus = DecisionStatus::NO_DECISION;
      }
      return true;
    }
    // assertions should all be satisfied, otherwise we are in conflict
    Assert(currValue == SAT_VALUE_TRUE);
    if (doWatchStatus)
    {
      // mark that we did not find a decision in it
      notifyStatus(fromIndex, DecisionStatus::NO_DECISION);
    }
    // already justified, immediately skip
    curr = al.getNextAssertion(fromIndex);
  }
  return false;
}

void JustificationStrategy::notifyStatus(size_t i, DecisionStatus s)
{
  // TODO: update order
  Trace("jh-status") << "Assertion #" << i << " had status " << s << std::endl;
  switch (s)
  {
    case DecisionStatus::BACKTRACK:
    {
      ++(d_stats.d_numStatusBacktrack);
      // erase from backtrack queue if already there
      // add to front of backtrack queue
    }
    break;
    case DecisionStatus::DECISION:
    {
      ++(d_stats.d_numStatusDecision);
      // add to decision queue if not there already
    }
    break;
    case DecisionStatus::NO_DECISION:
    {
      ++(d_stats.d_numStatusNoDecision);
      // erase from backtrack queue if already there
      // erase from decision queue if already there
    }
    break;
    default: Unhandled(); break;
  }
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
