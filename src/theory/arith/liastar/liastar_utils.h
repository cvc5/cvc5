/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility functions for liastar extension.
 */

#ifdef CVC5_USE_NORMALIZ

#ifndef CVC5__THEORY__LIASTAR__UTILS_H
#define CVC5__THEORY__LIASTAR__UTILS_H

#include "expr/node.h"
#include "smt/env.h"
#include "theory/arith/liastar/liastar_stats.h"
#include "theory/arith/linear/normal_form.h"
#include "util/result.h"
namespace cvc5::internal {
namespace theory {
namespace arith {
namespace liastar {

/**
 * The integer type used by Normaliz. Note this shadows
 * cvc5::internal::Integer within namespace liastar.
 */
typedef mpz_class Integer;

/**
 * Utilities shared by the liastar extension: destructuring star-contains
 * atoms, converting their predicates to DNF, deciding satisfiability of
 * candidate disjuncts with a subsolver, and translating disjuncts into the
 * symbolic constraints Normaliz consumes.
 *
 * All methods are static and stateless. Methods taking a LiaStarStatistics
 * pointer accumulate timers and counters into it when it is non-null.
 */
class LiaStarUtils
{
 public:
  /**
   * Destructure a star-contains atom into the predicate its vector must
   * satisfy, by instantiating the lambda with the vector elements.
   *
   * The first child may be a purified skolem or a function array constant
   * rather than a syntactic lambda; both are resolved, see
   * uf::FunctionConst::getDefinition.
   *
   * The type rule of int.star-contains does not require its first argument
   * to be a lambda; this is enforced by TheoryArith::ppStaticRewrite. Callers
   * that may see atoms that were not preprocessed, e.g. the rewriter, must
   * check that getDefinition(n[0]) is non-null before calling this method.
   *
   * @param n a node of the form
   * (int.star-contains (lambda ((x_1 Int) ... (x_n Int)) p) y_1 ... y_n)
   * @param nm the node manager
   * @return the pair <(p y_1 ... y_n), (and (>= y_1 0) ... (>= y_n 0))>,
   * i.e. the instantiated predicate and the nonnegativity constraints on
   * the vector elements
   */
  static std::pair<Node, Node> getVectorPredicate(Node n, NodeManager* nm);
  /**
   * Check whether a conjunction of assertions is unsatisfiable, using either
   * cvc5 or Normaliz as the subsolver depending on the
   * arith-liastar-subsolver-normaliz-as-subsolver option. Free variables of
   * the assertions are existentially quantified.
   *
   * @param assertions the assertions to check, interpreted conjunctively
   * @param e the environment, used for its node manager and options
   * @param stats optional statistics collector, may be nullptr
   * @return unsat if the assertions were shown unsatisfiable, sat if they
   * were shown satisfiable, and none or unknown otherwise. In particular
   * none is returned without calling a subsolver when the
   * arith-liastar-subsolver option is disabled, so callers must treat any
   * status other than unsat as "not known to be unsat".
   */
  static Result areAssertionsUnsat(const std::vector<Node>& assertions,
                                   Env* e,
                                   LiaStarStatistics* stats = nullptr);

  /**
   * Check satisfiability of an assertion with a cvc5 subsolver, existentially
   * quantifying the given free variables. If the
   * arith-liastar-assume-nonnegative option is enabled, the variables are
   * additionally constrained to be nonnegative.
   *
   * @param freeVariables the free variables of the assertion to quantify, may
   * be empty in which case the assertion is checked as is
   * @param assertion the assertion to check
   * @param e the environment, used for its node manager and options
   * @param stats optional statistics collector, may be nullptr
   * @return the status reported by the subsolver
   */
  static Result cvc5CheckSat(const std::vector<Node>& freeVariables,
                             Node assertion,
                             Env* e,
                             LiaStarStatistics* stats = nullptr);
  /**
   * Check satisfiability of a conjunction of LIA constraints by computing its
   * cone with Normaliz: the constraints are unsatisfiable over the integers
   * exactly when the resulting inhomogeneous cone is empty.
   *
   * @param variables a node of Kind BOUND_VAR_LIST giving the coordinates of
   * the ambient space, in order
   * @param assertion a conjunction of LIA constraints over `variables`
   * @param assumeNonnegative whether to restrict the cone to the nonnegative
   * orthant; when false every coordinate is sign-unrestricted
   * @param stats optional statistics collector, may be nullptr
   * @return unsat if the cone is empty, and none otherwise (a nonempty cone
   * is not reported as sat, since satisfiability is not needed by callers)
   */
  static Result normalizCheckSat(Node variables,
                                 Node assertion,
                                 bool assumeNonnegative,
                                 LiaStarStatistics* stats = nullptr);

  /**
   * This function returns a list of matrices representing cones (disjunctions)
   * where the rows of each matrix are constraints of the form a1 x_1 + ... +
   * an_xn + b >= 0
   * @param variables is a node of Kind BOUND_VAR_LIST
   * @param n is a LIA predicate in DNF format
   * @return one pair per disjunct of n, holding the disjunct's constraints as
   * Normaliz symbolic constraint strings (over the coordinates x[1]..x[k] of
   * `variables`) together with the disjunct itself
   */
  static std::vector<std::pair<std::vector<std::string>, Node>> getMatrices(
      Node variables, Node n);

 private:
  /**
   * Print a linear polynomial as a Normaliz symbolic term, mapping the i-th
   * variable of `variables` to the Normaliz coordinate x[i + 1].
   *
   * @param variables a node of Kind BOUND_VAR_LIST giving the coordinate
   * order; every variable of p must occur in it
   * @param p an integral linear polynomial
   * @return the polynomial as a string, e.g. "2x[1] - x[3] + 5"
   */
  static std::string getString(Node variables, linear::Polynomial& p);
};
}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__LIASTAR__UTILS_H */

#endif /* CVC5_USE_NORMALIZ */