/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The solver for quantifier elimination queries.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__QUANT_ELIM_SOLVER_H
#define CVC5__SMT__QUANT_ELIM_SOLVER_H

#include "expr/node.h"
#include "smt/assertions.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace smt {

class SmtSolver;
class ContextManager;

/**
 * A solver for quantifier elimination queries.
 *
 * This class is responsible for responding to get-qe and get-qe-partial
 * commands. It uses an underlying SmtSolver, which it queries for
 * quantifier instantiations used for unsat which are in turn used for
 * constructing the solution for the quantifier elimination query.
 */
class QuantElimSolver : protected EnvObj
{
 public:
  QuantElimSolver(Env& env, SmtSolver& sms, ContextManager* ctx);
  ~QuantElimSolver();

  /**
   * This function takes as input a quantified formula q
   * of the form:
   *   Q x1...xn. P( x1...xn, y1...yn )
   * where P( x1...xn, y1...yn ) is a quantifier-free
   * formula in a logic that supports quantifier elimination.
   * Currently, the only logics fully supported by quantifier
   * elimination is LRA and LIA, although this method can be invoked in
   * any logic.
   *
   * This function returns a formula ret such that, given
   * the current set of formulas A asserted to the SolverEngine :
   *
   * If doFull = true, then
   *   - ( A ^ q ) and ( A ^ ret ) are equivalent
   *   - ret is quantifier-free formula containing
   *     only free variables in y1...yn.
   *
   * If doFull = false, then
   *   - (A ^ q) => (A ^ ret) if Q is forall or
   *     (A ^ ret) => (A ^ q) if Q is exists,
   *   - ret is quantifier-free formula containing
   *     only free variables in y1...yn,
   *   - If Q is exists, let A^Q_n be the formula
   *       A ^ ~ret^Q_1 ^ ... ^ ~ret^Q_n
   *     where for each i=1,...n, formula ret^Q_i
   *     is the result of calling doQuantifierElimination
   *     for q with the set of assertions A^Q_{i-1}.
   *     Similarly, if Q is forall, then let A^Q_n be
   *       A ^ ret^Q_1 ^ ... ^ ret^Q_n
   *     where ret^Q_i is the same as above.
   *     In either case, we have that ret^Q_j will
   *     eventually be true or false, for some finite j.
   *
   * The former feature is quantifier elimination, and
   * is run on invocations of the smt2 extended command get-qe.
   * The latter feature is referred to as partial quantifier
   * elimination, and is run on invocations of the smt2
   * extended command get-qe-disjunct, which can be used
   * for incrementally computing the result of a
   * quantifier elimination.
   *
   * @param q The quantified formula we are eliminating quantifiers from
   * @param doFull Whether we are doing full quantifier elimination on q
   * @param isInternalSubsolver Whether the SolverEngine we belong to is an
   * internal subsolver. If it is not, then we convert the final result to
   * witness form.
   * @return The result of eliminating quantifiers from q.
   */
  Node getQuantifierElimination(Node q, bool doFull, bool isInternalSubsolver);

 private:
  /** The SMT solver, which is used during doQuantifierElimination. */
  SmtSolver& d_smtSolver;
  /** The underlying context manager. */
  ContextManager* d_ctx;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif /* CVC5__SMT__QUANT_ELIM_SOLVER_H */
