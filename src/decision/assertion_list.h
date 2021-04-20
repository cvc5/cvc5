/*********************                                                        */
/*! \file assertion_list.h
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

#include "cvc5_private.h"

#ifndef CVC5__DECISION__ASSERTION_LIST_H
#define CVC5__DECISION__ASSERTION_LIST_H

#include <iosfwd>

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5 {
namespace decision {

/**
 * For monitoring activity of assertions
 */
enum class DecisionStatus
{
  // not currently watching status of the current assertion
  INACTIVE,
  // no decision was made considering the assertion
  NO_DECISION,
  // a decision was made considering the assertion
  DECISION,
  // we backtracked while considering the assertion
  BACKTRACK
};
const char* toString(DecisionStatus s);
std::ostream& operator<<(std::ostream& out, DecisionStatus s);

class AssertionList
{
 public:
  AssertionList(context::Context* ac,
                context::Context* ic,
                bool useDyn = false);
  virtual ~AssertionList() {}
  /** Presolve, which clears the dynamic assertion order */
  void presolve();
  /** Add the assertion */
  void addAssertion(TNode n);
  /**
   * Get the new assertion, increment d_assertionIndex, sets fromIndex to the
   * index of the assertion.
   */
  TNode getNextAssertion();
  /** size */
  size_t size() const;
  /** Notify status */
  void notifyStatus(TNode n, DecisionStatus s);

 private:
  /** The list of assertions */
  context::CDList<Node> d_assertions;
  /** The index of the next assertion to satify */
  context::CDO<size_t> d_assertionIndex;
  // --------------------------- dynamic assertions
  /** are we using dynamic assertions? */
  bool d_usingDynamic;
  /** The list of assertions */
  std::vector<TNode> d_dlist;
  /** The index of the next assertion to satify */
  context::CDO<size_t> d_dindex;
};

}  // namespace decision
}  // namespace cvc5

#endif /* CVC5__DECISION__ASSERTION_LIST_H */
