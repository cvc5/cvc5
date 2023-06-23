/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of assertion list
 */

#include "decision/assertion_list.h"

namespace cvc5::internal {
namespace decision {

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

AssertionList::AssertionList(context::Context* ac,
                             context::Context* ic,
                             bool useDyn)
    : d_assertions(ac),
      d_assertionIndex(ic),
      d_usingDynamic(useDyn),
      d_dindex(ic)
{
}

void AssertionList::presolve()
{
  Trace("jh-status") << "AssertionList::presolve" << std::endl;
  d_assertionIndex = 0;
  d_dlist.clear();
  d_dindex = 0;
}

void AssertionList::addAssertion(TNode n) { d_assertions.push_back(n); }

TNode AssertionList::getNextAssertion()
{
  size_t fromIndex;
  if (d_usingDynamic)
  {
    // is a dynamic assertion ready?
    fromIndex = d_dindex.get();
    if (fromIndex < d_dlist.size())
    {
      d_dindex = d_dindex.get() + 1;
      Trace("jh-status") << "Assertion " << d_dlist[fromIndex].getId()
                         << " from dynamic list" << std::endl;
      return d_dlist[fromIndex];
    }
  }
  // check if dynamic assertions
  fromIndex = d_assertionIndex.get();
  Assert(fromIndex <= d_assertions.size());
  if (fromIndex == d_assertions.size())
  {
    return Node::null();
  }
  // increment for the next iteration
  d_assertionIndex = d_assertionIndex + 1;
  Trace("jh-status") << "Assertion " << d_assertions[fromIndex].getId()
                     << std::endl;
  return d_assertions[fromIndex];
}
size_t AssertionList::size() const { return d_assertions.size(); }

void AssertionList::notifyStatus(TNode n, DecisionStatus s)
{
  Trace("jh-status") << "Assertion status " << s << " for " << n.getId()
                     << ", current " << d_dindex.get() << "/" << d_dlist.size()
                     << std::endl;
  if (!d_usingDynamic)
  {
    // not using dynamic ordering, return
    return;
  }
  if (s == DecisionStatus::NO_DECISION)
  {
    // no decision does not impact the decision order
    return;
  }
  std::unordered_set<TNode>::iterator it = d_dlistSet.find(n);
  if (s == DecisionStatus::DECISION)
  {
    if (it == d_dlistSet.end())
    {
      // if we just had a status on an assertion and it didn't occur in dlist,
      // then our index should have exhausted dlist
      Assert(d_dindex.get() == d_dlist.size());
      if (d_dindex.get() == d_dlist.size())
      {
        d_dindex = d_dindex.get() + 1;
      }
      // add to back of the decision list if not already there
      d_dlist.push_back(n);
      d_dlistSet.insert(n);
      Trace("jh-status") << "...push due to decision" << std::endl;
    }
    return;
  }
  if (s == DecisionStatus::BACKTRACK)
  {
    // backtrack inserts at the current position
    if (it == d_dlistSet.end())
    {
      d_dlist.insert(d_dlist.begin(), n);
      d_dlistSet.insert(n);
    }
  }
}

}  // namespace decision
}  // namespace cvc5::internal
