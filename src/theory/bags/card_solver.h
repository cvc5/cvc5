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
 * Cardinality solver for theory of bags.
 */

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "cvc5_private.h"
#include "smt/env_obj.h"
#include "theory/bags/bag_reduction.h"

#ifndef CVC5__THEORY__CARD__SOLVER_H
#define CVC5__THEORY__CARD__SOLVER_H

#include "theory/bags/inference_generator.h"

namespace cvc5 {
namespace theory {
namespace bags {

class InferenceManager;
class SolverState;
class TermRegistry;

/** The cardinality solver for the theory of bags
 *
 */
class CardSolver : protected EnvObj
{
 public:
  CardSolver(Env& env, SolverState& s, InferenceManager& im);
  ~CardSolver();

  /**
   * add lemmas related to cardinality constraints
   */
  void checkCardinalityGraph();

 private:
  /** apply inference rules for empty bags */
  void checkEmpty(const Node& cardTerm, const Node& n);
  /** apply inference rules for bag make */
  void checkBagMake(const Node& cardTerm, const Node& n);
  /** apply inference rules for union disjoint */
  void checkUnionDisjoint(const Node& cardTerm, const Node& n);
  /** apply inference rules for union max */
  void checkUnionMax(const Node& cardTerm, const Node& n);
  /** apply inference rules for intersection_min operator */
  void checkIntersectionMin(const Node& cardTerm, const Node& n);
  /** apply inference rules for difference subtract */
  void checkDifferenceSubtract(const Node& cardTerm, const Node& n);
  /** apply inference rules for difference remove */
  void checkDifferenceRemove(const Node& cardTerm, const Node& n);
  /** apply inference rules for leaves in the cardinality graph
   *
   */
  void reduceCardinality(const Node& cardTerm);
  /** The solver state object */
  SolverState& d_state;
  /** The inference generator object*/
  InferenceGenerator d_ig;
  /** Reference to the inference manager for the theory of bags */
  InferenceManager& d_im;
  /** bag reduction */
  BagReduction d_bagReduction;

  /** Commonly used constants */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
}; /* class CardSolver */

}  // namespace bags
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__CARD__SOLVER_H */
