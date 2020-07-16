/*********************                                                        */
/*! \file abduction_solver.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The solver for abduction queries
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__ABDUCTION_SOLVER_H
#define CVC4__SMT__ABDUCTION_SOLVER_H

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * A solver for abduction queries.
 *
 * This class is responsible for responding to get-abduct commands. It spawns
 * a subsolver SmtEngine for a sygus conjecture that captures the abduction
 * query, and implements supporting utility methods such as checkAbduct.
 */
class AbductionSolver
{
 public:
  AbductionSolver(SmtEngine* parent);
  ~AbductionSolver();
  /**
   * This method asks this SMT engine to find an abduct with respect to the
   * current assertion stack (call it A) and the goal (call it B).
   * If this method returns true, then abd is set to a formula C such that
   * A ^ C is satisfiable, and A ^ ~B ^ C is unsatisfiable.
   *
   * @param goal The goal of the abduction problem.
   * @param grammarType A sygus datatype type that encodes the syntax
   * restrictions on the shape of possible solutions.
   * @param abd This argument is updated to contain the solution to the
   * abduction problem. Notice that this is a formula whose free symbols
   * are contained in goal + the parent's current assertion stack.
   *
   * This method invokes a separate copy of the SMT engine for solving the
   * corresponding sygus problem for generating such a solution.
   */
  bool getAbduct(const Node& goal, const TypeNode& grammarType, Node& abd);

  /**
   * Same as above, but without user-provided grammar restrictions. A default
   * grammar is chosen internally using the sygus grammar constructor utility.
   */
  bool getAbduct(const Node& goal, Node& abd);

  /**
   * Check that a solution to an abduction conjecture is indeed a solution.
   *
   * The check is made by determining that the assertions conjoined with the
   * solution to the abduction problem (a) is SAT, and the assertions conjoined
   * with the abduct and the goal is UNSAT. If these criteria are not met, an
   * internal error is thrown.
   */
  void checkAbduct(Node a);

 private:
  /**
   * Get abduct internal.
   *
   * Get the next abduct from the internal subsolver d_subsolver. If
   * successful, this method returns true and sets abd to that abduct.
   *
   * This method assumes d_subsolver has been initialized to do abduction
   * problems.
   */
  bool getAbductInternal(Node& abd);
  /** The parent SMT engine */
  SmtEngine* d_parent;
  /** The SMT engine subsolver
   *
   * This is a separate copy of the SMT engine which is used for making
   * calls that cannot be answered by this copy of the SMT engine. An example
   * of invoking this subsolver is the get-abduct command, where we wish to
   * solve a sygus conjecture based on the current assertions. In particular,
   * consider the input:
   *   (assert A)
   *   (get-abduct B)
   * In the copy of the SMT engine where these commands are issued, we maintain
   * A in the assertion stack. To solve the abduction problem, instead of
   * modifying the assertion stack to remove A and add the sygus conjecture
   * (exists I. ...), we invoke a fresh copy of the SMT engine and leave the
   * assertion stack unchaged. This copy of the SMT engine can be further
   * queried for information regarding further solutions.
   */
  std::unique_ptr<SmtEngine> d_subsolver;
  /**
   * The conjecture of the current abduction problem. This expression is only
   * valid while the parent SmtEngine is in mode SMT_MODE_ABDUCT.
   */
  Node d_abdConj;
  /**
   * If applicable, the function-to-synthesize that the subsolver is solving
   * for. This is used for the get-abduct command.
   */
  Node d_sssf;
};

}  // namespace smt
}  // namespace CVC4

#endif /* CVC4__SMT__ABDUCTION_SOLVER_H */
