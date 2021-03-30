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

AssertionList::AssertionList(context::Context* ac, context::Context* ic)
    : d_assertions(ac), d_assertionIndex(ic)
{
}

void AssertionList::addAssertion(TNode n) { d_assertions.push_back(n); }

TNode AssertionList::getNextAssertion(size_t& fromIndex)
{
  fromIndex = d_assertionIndex.get();
  Assert(fromIndex <= d_assertions.size());
  if (fromIndex == d_assertions.size())
  {
    return Node::null();
  }
  // increment for the next iteration
  d_assertionIndex = d_assertionIndex + 1;
  return d_assertions[fromIndex];
}

DynamicAssertionList::DynamicAssertionList(context::Context* ic) : d_assertionIndex(ic)
{
  
}

TNode DynamicAssertionList::getNextAssertion()
{
  return TNode::null();
}

}  // namespace CVC4
