/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for abduction queries.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__ABDUCTION_SOLVER_H
#define CVC5__SMT__ABDUCTION_SOLVER_H

#include "expr/node.h"
#include "expr/type_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class SolverEngine;

namespace smt {

/**
 * A solver for abduction queries.
 *
 * This class is responsible for responding to get-abduct commands. It spawns
 * a subsolver SolverEngine for a sygus conjecture that captures the abduction
 * query, and implements supporting utility methods such as checkAbduct.
 */
class AbductionSolver : protected EnvObj
{
 public:
  AbductionSolver(Env& env);
  ~AbductionSolver();
  /**
   * This method asks this SMT engine to find an abduct with respect to the
   * current assertion stack (call it A) and the goal (call it B).
   * If this method returns true, then abd is set to a formula C such that
   * A ^ C is satisfiable, and A ^ ~B ^ C is unsatisfiable.
   *
   * @param axioms The expanded assertions A of the parent SMT engine
   * @param goal The goal B of the abduction problem.
   * @param grammarType A sygus datatype type that encodes the syntax
   * restrictions on the shape of possible solutions.
   * @param abd This argument is updated to contain the solution C to the
   * abduction problem. Notice that this is a formula whose free symbols
   * are contained in goal + the parent's current assertion stack.
   * @return true if the abduct was successfully computed
   *
   * This method invokes a separate copy of the SMT engine for solving the
   * corresponding sygus problem for generating such a solution.
   */
  bool getAbduct(const std::vector<Node>& axioms,
                 const Node& goal,
                 const TypeNode& grammarType,
                 Node& abd);

  /**
   * Get the next abduct, return true if successful and store the result
   * in abd if so.
   * 
   * @param abd This argument is updated to contain the solution C to the
   * abduction problem.
   * @return true if the abduct was successfully computed
   */
  bool getAbductNext(Node& abd);

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
  /**
   * Check that a solution to an abduction conjecture is indeed a solution.
   *
   * The check is made by determining that the assertions conjoined with the
   * solution to the abduction problem (a) is SAT, and the assertions conjoined
   * with the abduct and the goal is UNSAT. If these criteria are not met, an
   * internal error is thrown. We use the expanded assertions of the parent SMT
   * engine, which are stored in d_axioms.
   *
   * @param a The abduct to check.
   */
  void checkAbduct(Node a);
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
  std::unique_ptr<SolverEngine> d_subsolver;
  /**
   * The conjecture of the current abduction problem. This expression is only
   * valid while the parent SolverEngine is in mode SMT_MODE_ABDUCT.
   */
  Node d_abdConj;
  /**
   * If applicable, the function-to-synthesize that the subsolver is solving
   * for. This is used for the get-abduct command.
   */
  Node d_sssf;
  /** The list of axioms for the abduction query */
  std::vector<Node> d_axioms;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__ABDUCTION_SOLVER_H */
