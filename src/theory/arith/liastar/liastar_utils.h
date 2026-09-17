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
   * rather than a syntactic lambda; both are resolved.
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
   * Convert a LIA predicate to disjunctive normal form, by eliminating ite
   * terms, converting to negation normal form, and distributing conjunctions
   * over disjunctions.
   *
   * @param n a node in LIA that only contains =, >=, ite in its tree
   * @param e the environment, used for its node manager, rewriter and options
   * @param stats optional statistics collector, may be nullptr
   * @return an equivalent node in DNF where ite and = are eliminated
   */
  static Node toDNF(Node n, Env* e, LiaStarStatistics* stats = nullptr);

  /**
   * Eliminate ite terms from a LIA predicate. An integer ite is replaced by a
   * disjunction over its branches, each guarded by the ite condition, so no
   * new variables are introduced.
   *
   * @param n a node in LIA that only contains =, >=, ite in its tree
   * @param e the environment, used for its node manager, rewriter and options
   * @param stats optional statistics collector, may be nullptr
   * @return an equivalent node that does not contain ite expressions
   * without introducing new variables
   */
  static Node removeItes(Node n, Env* e, LiaStarStatistics* stats = nullptr);

  /**
   * Distribute conjunctions over disjunctions, turning a negation-normal-form
   * predicate into DNF. Disjuncts that the subsolver shows to be unsat are
   * dropped, which keeps the result small enough for the cone computation.
   *
   * @param n a node in negation normal form whose atoms are LIA constraints
   * @param e the environment, used for its node manager, rewriter and options
   * @param stats optional statistics collector, may be nullptr
   * @param context conjuncts known to hold wherever n occurs (the accumulated
   * non-OR conjuncts of ancestor conjunctions). Used only to strengthen the
   * pruning subsolver checks; it is never part of the returned DNF.
   * @return an equivalent node in DNF
   */
  static Node distribute(Node n,
                         Env* e,
                         LiaStarStatistics* stats = nullptr,
                         const std::vector<Node>& context = {});

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
   * Enumerate the ite-free forms of an integer term. Each ite is expanded
   * into its two branches, so a term with k (independent) ites yields 2^k
   * cases.
   *
   * @param n an integer term
   * @param e the environment, used for its node manager and rewriter
   * @param stats optional statistics collector, may be nullptr
   * @return pairs <condition, term> whose conditions are pairwise disjoint
   * and cover all cases, where `term` is the value of n under `condition` and
   * contains no ite. For example (+ (ite c1 a b) (ite c2 c d)) yields
   * <(and c1 c2), (+ a c)>, <(and c1 (not c2)), (+ a d)>,
   * <(and (not c1) c2), (+ b c)> and <(and (not c1) (not c2)), (+ b d)>.
   */
  static std::vector<std::pair<Node, Node>> removeIntegerItes(
      Node n, Env* e, LiaStarStatistics* stats = nullptr);
  /**
   * Convert a predicate to negation normal form and eliminate the negations
   * of LIA atoms by flipping their relation, e.g. (not (>= a b)) becomes
   * (< a b), so that the result is a conjunction/disjunction structure over
   * unnegated atoms.
   *
   * @param n a Boolean node whose atoms are LIA constraints
   * @param e the environment, used for its node manager
   * @return an equivalent node in negation normal form with no negated atoms
   */
  static Node removeNot(Node n, Env* e);
  /**
   * Flatten a node and, one level down, each of its children by their own
   * kinds. A single expr::algorithm::flatten call only flattens nesting of
   * the node's own kind, so for an alternating structure this additionally
   * flattens the children: (or (and a (and b c)) d) becomes
   * (or (and a b c) d).
   *
   * @param nm the node manager
   * @param n the node to flatten
   * @return the flattened node, or n itself if it has no children
   */
  static Node recursiveFlatten(NodeManager* nm, Node n);
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