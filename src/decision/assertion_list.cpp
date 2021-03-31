/*********************                                                        */
/*! \file assertion_list.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Assertion list for justification strategy
 **/

#include "decision/assertion_list.h"

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

AssertionList::AssertionList(context::Context* ac, context::Context* ic)
    : d_assertions(ac), d_assertionIndex(ic), d_dindex(ic)
{
}

void AssertionList::addAssertion(TNode n) { d_assertions.push_back(n); }

TNode AssertionList::getNextAssertion()
{
  size_t fromIndex = d_assertionIndex.get();
  Assert(fromIndex <= d_assertions.size());
  if (fromIndex == d_assertions.size())
  {
    return Node::null();
  }
  // increment for the next iteration
  d_assertionIndex = d_assertionIndex + 1;
  return d_assertions[fromIndex];
}
size_t AssertionList::size() const { return d_assertions.size(); }

void AssertionList::notifyStatus(TNode n, DecisionStatus s)
{
  Trace("jh-status") << "Assertion status " << s << " for " << n << std::endl;
  switch (s)
  {
    case DecisionStatus::BACKTRACK:
    {
      // erase from backtrack queue if already there
      // add to front of backtrack queue
    }
    break;
    case DecisionStatus::DECISION:
    {
      // add to decision queue if not there already
    }
    break;
    case DecisionStatus::NO_DECISION:
    {
      // erase from backtrack queue if already there
      // erase from decision queue if already there
    }
    break;
    default: Unhandled(); break;
  }
}

}  // namespace CVC4
