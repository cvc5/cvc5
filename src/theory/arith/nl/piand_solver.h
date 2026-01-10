/******************************************************************************
 * Top contributors (to current version):
 *   Zvika Berger
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Solver for parametric integer and (PIAND) constraints.
 */

#ifndef CVC5__THEORY__ARITH__NL__PIAND_SOLVER_H
#define CVC5__THEORY__ARITH__NL__PIAND_SOLVER_H

#include <map>
#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/iand_utils.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class ArithState;
class InferenceManager;

namespace nl {

class NlModel;

/** parametric Integer and solver class
 *
 */
class PIAndSolver : protected EnvObj
{
  using NodeSet = context::CDHashSet<Node>;

 public:
  PIAndSolver(Env& env, InferenceManager& im, NlModel& model);
  ~PIAndSolver();

  /** init last call
   *
   * This is called at the beginning of last call effort check, where
   * assertions are the set of assertions belonging to arithmetic,
   * false_asserts is the subset of assertions that are false in the current
   * model, and xts is the set of extended function terms that are active in
   * the current context.
   */
  void initLastCall(const std::vector<Node>& assertions,
                    const std::vector<Node>& false_asserts,
                    const std::vector<Node>& xts);

  //-------------------------------------------- lemma schemas
  /** check initial refine
   *
   * Returns a set of valid theory lemmas, based on simple facts about PIAND.
   *
   * Examples:
   *
   * 0 <= piand(k,x,y) < 2^k
   * piand(k,x,y) <= x
   * piand(k,x,y) <= y
   * x=y => piand(k,x,y)=x
   *
   * This should be a heuristic incomplete check that only introduces a
   * small number of new terms in the lemmas it returns.
   */
  void checkInitialRefine();

  /** check full refine
   *
   * This should be a complete check that returns at least one lemma to
   * rule out the current model.
   */
  void checkFullRefine();

  //-------------------------------------------- end lemma schemas
 private:
  // The inference manager that we push conflicts and lemmas to.
  InferenceManager& d_im;

  /** Reference to the non-linear model object */
  NlModel& d_model;

  /** commonly used terms */
  Node d_false;
  Node d_true;
  Node d_zero;
  Node d_one;
  Node d_two;

  IAndUtils d_iandUtils;
  /** PIAND terms that have been given initial refinement lemmas */

  NodeSet d_initRefine;
  /** all PIAND terms, for each bit-width */

  std::map<Node, std::vector<Node>> d_piands;

  /**
   * Value-based refinement lemma for i of the form (piand k x y). Returns:
   *   x = M(x) ^ y = M(y) =>
   *     (piand k x y) = rewrite((piand k M(x) M(y)))
   */
  Node valueBasedLemma(Node i);

  /**
   * Sum-based refinement lemma for i of the form ((_ piand k) x y). Returns:
   * i = 2^0*min(x[0],y[0])+...2^{k-1}*min(x[k-1],y[k-1])
   * where x[i] is x div i mod 2
   * and min is defined with an ite.
   */
  Node sumBasedLemma(Node i, Kind kind);
}; /* class PIAndSolver */

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__PIAND_SOLVER_H */
