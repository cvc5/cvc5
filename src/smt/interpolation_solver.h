/*********************                                                        */
/*! \file interpolation_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Ying Sheng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for interpolation queries
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__INTERPOLATION_SOLVER_H
#define CVC4__SMT__INTERPOLATION_SOLVER_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * A solver for interpolation queries.
 *
 * This class is responsible for responding to get-interpol commands. It spawns
 * a subsolver SmtEngine for a sygus conjecture that captures the interpolation
 * query, and implements supporting utility methods such as checkInterpol.
 */
class InterpolationSolver
{
 public:
  InterpolationSolver(SmtEngine* parent);
  ~InterpolationSolver();

  /**
   * This method asks this SMT engine to find an interpolant with respect to
   * the current assertion stack (call it A) and the conjecture (call it B). If
   * this method returns true, then interpolant is set to a formula I such that
   * A ^ ~I and I ^ ~B are both unsatisfiable.
   *
   * @param conj The conjecture of the interpolation problem.
   * @param grammarType A sygus datatype type that encodes the syntax
   * restrictions on the shape of possible solutions.
   * @param interpol This argument is updated to contain the solution to the
   * interpolation problem.
   *
   * This method invokes a separate copy of the SMT engine for solving the
   * corresponding sygus problem for generating such a solution.
   */
  bool getInterpol(const Node& conj,
                   const TypeNode& grammarType,
                   Node& interpol);

  /**
   * Same as above, but without user-provided grammar restrictions. A default
   * grammar is chosen internally using the sygus grammar constructor utility.
   */
  bool getInterpol(const Node& conj, Node& interpol);

  /**
   * Check that a solution to an interpolation problem is indeed a solution.
   *
   * The check is made by determining that the assertions imply the solution of
   * the interpolation problem (interpol), and the solution implies the goal
   * (conj). If these criteria are not met, an internal error is thrown.
   */
  void checkInterpol(Expr interpol,
                     const std::vector<Expr>& easserts,
                     const Node& conj);

 private:
  /** The parent SMT engine */
  SmtEngine* d_parent;
};

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__INTERPOLATION_SOLVER_H */
