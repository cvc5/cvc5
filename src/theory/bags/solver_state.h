/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Bags state object.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAGS__THEORY_SOLVER_STATE_H
#define CVC5__THEORY__BAGS__THEORY_SOLVER_STATE_H

#include <map>

#include "theory/theory_state.h"

namespace cvc5 {
namespace theory {
namespace bags {

class SolverState : public TheoryState
{
 public:
  SolverState(Env& env, Valuation val);

  /**
   * This function adds the bag representative n to the set d_bags if it is not
   * already there. This function is called during postCheck to collect bag
   * terms in the equality engine. See the documentation of
   * @link SolverState::collectBagsAndCountTerms
   */
  void registerBag(TNode n);

  /**
   * @param n has the form (bag.count e A)
   * @pre bag A needs is already registered using registerBag(A)
   * @return a unique skolem for (bag.count e A)
   */
  void registerCountTerm(TNode n);
  /** get all bag terms that are representatives in the equality engine.
   * This function is valid after the current solver is initialized during
   * postCheck. See SolverState::initialize and BagSolver::postCheck
   */
  const std::set<Node>& getBags();
  /**
   * @pre B is a registered bag
   * @return all elements associated with bag B so far
   * Note that associated elements are not necessarily elements in B
   * Example:
   * (assert (= 0 (bag.count x B)))
   * element x is associated with bag B, albeit x is definitely not in B.
   */
  const std::set<Node>& getElements(Node B);
  /** initialize bag and count terms */
  void initialize();
  /** return disequal bag terms */
  const std::set<Node>& getDisequalBagTerms();

 private:
  /** clear all bags data structures */
  void reset();
  /**
   * collect bags' representatives and all count terms.
   * This function is called during postCheck
   */
  void collectBagsAndCountTerms();
  /**
   * collect disequal bag terms. This function is called during postCheck.
   */
  void collectDisequalBagTerms();
  /** constants */
  Node d_true;
  Node d_false;
  /** node manager for this solver state */
  NodeManager* d_nm;
  /** collection of bag representatives */
  std::set<Node> d_bags;
  /** bag -> associated elements */
  std::map<Node, std::set<Node>> d_bagElements;
  /** Disequal bag terms */
  std::set<Node> d_deq;
}; /* class SolverState */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BAGS__THEORY_SOLVER_STATE_H */
