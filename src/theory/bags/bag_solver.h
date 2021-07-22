/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for the theory of bags.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BAG__SOLVER_H
#define CVC5__THEORY__BAG__SOLVER_H

#include "theory/bags/inference_generator.h"

namespace cvc5 {
namespace theory {
namespace bags {

class InferenceManager;
class SolverState;
class TermRegistry;

/** The solver for the theory of bags
 *
 */
class BagSolver
{
 public:
  BagSolver(SolverState& s, InferenceManager& im, TermRegistry& tr);
  ~BagSolver();

  void postCheck();

 private:
  /** apply inference rules for empty bags */
  void checkEmpty(const Node& n);
  /**
   * apply inference rules for MK_BAG operator.
   * Example: Suppose n = (bag x c), and we have two count terms (bag.count x n)
   * and (bag.count y n).
   * This function will add inferences for the count terms as documented in
   * InferenceGenerator::mkBag.
   * Note that element y may not be in bag n. See the documentation of
   * SolverState::getElements.
   */
  void checkMkBag(const Node& n);
  /**
   * @param n is a bag that has the form (op A B)
   * @return the set union of known elements in (op A B) , A, and B.
   */
  std::set<Node> getElementsForBinaryOperator(const Node& n);
  /** apply inference rules for union disjoint */
  void checkUnionDisjoint(const Node& n);
  /** apply inference rules for union max */
  void checkUnionMax(const Node& n);
  /** apply inference rules for intersection_min operator */
  void checkIntersectionMin(const Node& n);
  /** apply inference rules for difference subtract */
  void checkDifferenceSubtract(const Node& n);
  /** apply inference rules for difference remove */
  void checkDifferenceRemove(const Node& n);
  /** apply inference rules for duplicate removal operator */
  void checkDuplicateRemoval(Node n);
  /** apply non negative constraints for multiplicities */
  void checkNonNegativeCountTerms(const Node& bag, const Node& element);
  /** apply inference rules for disequal bag terms */
  void checkDisequalBagTerms();

  /** The solver state object */
  SolverState& d_state;
  /** The inference generator object*/
  InferenceGenerator d_ig;
  /** Reference to the inference manager for the theory of bags */
  InferenceManager& d_im;
  /** Reference to the term registry of theory of bags */
  TermRegistry& d_termReg;
  /** Commonly used constants */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
}; /* class BagSolver */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__BAG__SOLVER_H */
