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
 * Assertion list
 */

#include "cvc5_private.h"

#ifndef CVC5__DECISION__ASSERTION_LIST_H
#define CVC5__DECISION__ASSERTION_LIST_H

#include <iosfwd>
#include <unordered_set>
#include <vector>

#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5::internal {
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

/**
 * An assertion list used by the justification heuristic. This tracks a list
 * of formulas that we must justify.
 */
class AssertionList
{
 public:
  /**
   * @param ac The context on which the assertions depends on. This is the
   * user context for assertions. It is the SAT context for assertions that
   * are dynamically relevant based on what is asserted, e.g. lemmas
   * corresponding to skolem definitions.
   * @param ic The context on which the current index of the assertions
   * depends on. This is typically the SAT context.
   * @param dyn Whether to use a dynamic ordering of the assertions. If this
   * flag is true, then getNextAssertion will return the most important next
   * assertion to consider based on heuristics in response to notifyStatus.
   */
  AssertionList(context::Context* ac,
                context::Context* ic,
                bool useDyn = false);
  virtual ~AssertionList() {}
  /** Presolve, which clears the dynamic assertion order */
  void presolve();
  /** Add the assertion n */
  void addAssertion(TNode n);
  /**
   * Get the next assertion and increment d_assertionIndex.
   */
  TNode getNextAssertion();
  /** Get the number of assertions */
  size_t size() const;
  /**
   * Notify status, which indicates the status of the assertion n, where n
   * is the assertion last returned by getNextAssertion above (independent of
   * the context). The status s indicates what happened when we were trying to
   * justify n. This impacts its order if useDyn is true.
   */
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
  /** The set of assertions for fast membership testing in the above vector */
  std::unordered_set<TNode> d_dlistSet;
  /** The index of the next assertion to satify */
  context::CDO<size_t> d_dindex;
};

}  // namespace decision
}  // namespace cvc5::internal

#endif /* CVC5__DECISION__ASSERTION_LIST_H */
