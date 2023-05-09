/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Ying Sheng, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for interpolation queries.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__INTERPOLATION_SOLVER_H
#define CVC5__SMT__INTERPOLATION_SOLVER_H

#include "expr/node.h"
#include "expr/type_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace theory {
namespace quantifiers {
class SygusInterpol;
}
}  // namespace theory

namespace smt {

/**
 * A solver for interpolation queries.
 *
 * This class is responsible for responding to get-interpolant commands. It
 * spawns a subsolver SolverEngine for a sygus conjecture that captures the
 * interpolation query, and implements supporting utility methods such as
 * checkInterpol.
 */
class InterpolationSolver : protected EnvObj
{
 public:
  InterpolationSolver(Env& env);
  ~InterpolationSolver();

  /**
   * This method asks this solver to find an interpolant with respect to
   * the current assertion stack (call it A) and the conjecture (call it B). If
   * this method returns true, then interpolant is set to a formula I such that
   * A ^ ~I and I ^ ~B are both unsatisfiable.
   *
   * @param axioms The expanded assertions A of the parent SMT engine
   * @param conj The conjecture B of the interpolation problem.
   * @param grammarType A sygus datatype type that encodes the syntax
   * restrictions on the shape of possible solutions.
   * @param interpol This argument is updated to contain the solution I to the
   * interpolation problem.
   *
   * This method invokes a separate copy of the SMT engine for solving the
   * corresponding sygus problem for generating such a solution.
   */
  bool getInterpolant(const std::vector<Node>& axioms,
                      const Node& conj,
                      const TypeNode& grammarType,
                      Node& interpol);

  /**
   * Get next interpolant. This can only be called immediately after a
   * successful call to getInterpolant or getInterpolantNext.
   *
   * Returns true if an interpolant was found, and sets interpol to the
   * interpolant.
   *
   * This method reuses the subsolver initialized by the last call to
   * getInterpolant.
   */
  bool getInterpolantNext(Node& interpol);

 private:
  /**
   * Check that a solution to an interpolation problem is indeed a solution.
   *
   * The check is made by determining that the assertions imply the solution of
   * the interpolation problem (interpol), and the solution implies the goal
   * (conj). If these criteria are not met, an internal error is thrown.
   */
  void checkInterpol(Node interpol,
                     const std::vector<Node>& easserts,
                     const Node& conj);

  /** The subsolver */
  std::unique_ptr<theory::quantifiers::SygusInterpol> d_subsolver;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__INTERPOLATION_SOLVER_H */
