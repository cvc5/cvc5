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

AssertionList::AssertionList(context::Context* ac, context::Context* ic, bool useDyn)
    : d_assertions(ac), d_assertionIndex(ic), d_usingDynamic(useDyn), d_dindex(ic)
{
}

void AssertionList::addAssertion(TNode n) { d_assertions.push_back(n); }

TNode AssertionList::getNextAssertion()
{
  size_t fromIndex;
  if (d_usingDynamic)
  {
    // is a dynamic assertion ready?
    fromIndex = d_dindex.get();
    if (fromIndex<d_dlist.size())
    {
      d_dindex = d_dindex.get() + 1;
      Trace("jh-status") << "Assertion " << d_dlist[fromIndex].getId() << " from dynamic list" << std::endl;
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
  Trace("jh-status") << "Assertion " << d_assertions[fromIndex].getId() << std::endl;
  return d_assertions[fromIndex];
}
size_t AssertionList::size() const { return d_assertions.size(); }

void AssertionList::notifyStatus(TNode n, DecisionStatus s)
{
  // FIXME
  Trace("jh-status") << "Assertion status " << s << " for " << n.getId() << ", current " << d_dindex.get() << "/" << d_dlist.size() << std::endl;
  if (!d_usingDynamic)
  {
    // not using dynamic ordering, return
    return;
  }
  if (s==DecisionStatus::NO_DECISION)
  {
    return;
  }
  std::vector<TNode>::iterator it = std::find(d_dlist.begin(), d_dlist.end(), n);
  if (s==DecisionStatus::DECISION)
  {
    if (it==d_dlist.end())
    {
      // if we just had status on an assertion and it didnt occur id dlist,
      // then our index should have exhausted dlist
      Assert (d_dindex.get()==d_dlist.size());
      if (d_dindex.get()==d_dlist.size())
      {
        d_dindex = d_dindex.get()+1;
      }
      // add to back of the decision list if not already there
      d_dlist.push_back(n);
      Trace("jh-status") << "...push due to decision" << std::endl;
    }
    return;
  }
  if (s==DecisionStatus::BACKTRACK)
  {
    if (it==d_dlist.end())
    {
      d_dlist.insert(d_dlist.begin(), n);
    }
    return;
  }
  // otherwise, remove if already there
  if (it!=d_dlist.end())
  {
    size_t index = static_cast<size_t>(std::distance(d_dlist.begin(),it));
    if (index<d_dindex.get())
    {
      // shift the current index
      d_dindex = d_dindex.get() - 1;
    }
    Trace("jh-status") << "...remove due to " << s << std::endl;
    d_dlist.erase(it);
  }
  // if we backtracked, insert as the next assertion
  if (s==DecisionStatus::BACKTRACK)
  {
    if (d_dindex.get()>=d_dlist.size())
    {
      Trace("jh-status") << "...push back due to backtrack" << std::endl;
      d_dlist.push_back(n);
      d_dindex = d_dlist.size();
    }
    else
    {
      Trace("jh-status") << "...insert due to backtrack" << std::endl;
      d_dlist.insert(d_dlist.begin() + d_dindex.get(), n);
      d_dindex = d_dindex + 1;
    }
  }
}

}  // namespace CVC4
