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
#include "expr/node_converter.h"
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
 * Converts the negated linear constraints of a predicate in negation normal
 * form into unnegated ones, since a Normaliz constraint cannot be negated:
 *   (not (>= a b)) --> (< a b)
 *   (not (= a b))  --> (or (> a b) (< a b))
 * Any other negation, e.g. (not p) for a Boolean variable p, is kept. Used
 * by LiaStarUtils::removeNot.
 */
class NegatedConstraintConverter : public NodeConverter
{
 public:
  NegatedConstraintConverter(NodeManager* nm);
  /**
   * @param n a term whose children are already converted
   * @return the unnegated form of n if n is a negated constraint, otherwise
   * n itself
   */
  Node postConvert(Node n) override;
};

/**
 * Eliminates the ites of a LIA predicate without introducing variables, see
 * LiaStarUtils::removeItes. A Boolean ite is expanded where it occurs:
 *   (ite c p q) --> (or (and p c) (and q (not c)))
 * An integer ite is kept until the atom containing it is converted, and the
 * atom is then split on its ites one at a time:
 *   (>= (ite c x y) 1) --> (or (and (>= x 1) c) (and (>= y 1) (not c)))
 * Terms are converted bottom-up, so by the time an atom is split the
 * conditions of its ites are ite-free.
 */
class IteEliminationConverter : public NodeConverter
{
 public:
  /**
   * @param e the environment, used for its node manager and rewriter
   * @param stats optional statistics collector, may be nullptr
   */
  IteEliminationConverter(Env& e, LiaStarStatistics* stats);
  /**
   * @param n a term whose children are already converted
   * @return an ite-free equivalent of n if n is Boolean, otherwise n itself
   */
  Node postConvert(Node n) override;

 private:
  /**
   * Split an atom on its ites: each split substitutes an ite by its branches
   * and guards them with its condition and its negation, until no ite is
   * left. Every occurrence of an ite is substituted at once, so a repeated
   * ite is split once:
   *   (>= (+ (ite c x y) (ite c x y)) 0)
   *   --> (or (and (>= (* 2 x) 0) c) (and (>= (* 2 y) 0) (not c)))
   * The changed integer children of the atom are rewritten to stay in the
   * arithmetic normal form getMatrices expects.
   *
   * @param atom a Boolean term with a non-Boolean child, whose ites have
   * ite-free conditions
   * @return the disjunction of the split atoms, each conjoined with its
   * guards
   */
  Node splitAtom(Node atom);
  /** Count ite in d_stats, once per ite eliminated by this converter. */
  void countEliminated(Node ite);
  /** The rewriter, used to normalize the changed integer terms */
  Rewriter* d_rewriter;
  /** Optional statistics collector, may be nullptr */
  LiaStarStatistics* d_stats;
  /** The ites counted so far */
  std::unordered_set<Node> d_eliminated;
};

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
   * Convert a LIA predicate to disjunctive normal form. Normaliz takes one
   * conjunction of linear constraints per cone, see getMatrices, so the
   * predicate of a star-contains atom is first brought into the form
   * (or (and a_1 a_2 ...) (and b_1 b_2 ...) ...) whose atoms are unnegated,
   * ite-free linear constraints.
   *
   * The steps are removeItes, removeNot and distribute, followed by
   * flattening; no new variables are introduced.
   *
   * @param n a Boolean combination (and, or, not) of linear integer
   * constraints (<, <=, =, >=, >) and Boolean variables, whose integer terms
   * may contain ite
   * @param e the environment, used for its node manager, rewriter and options
   * @param stats optional statistics collector, may be nullptr
   * @return an equivalent node in DNF: a disjunction of conjunctions of
   * atoms, or a single conjunction or atom, without ite and with negation
   * only on Boolean variables. Disjuncts the subsolver shows to be unsat
   * are dropped, see distribute.
   */
  static Node toDNF(Node n, Env& e, LiaStarStatistics* stats = nullptr);

  /**
   * Eliminate ite from a LIA predicate. cvc5's ite removal would introduce
   * fresh variables, and every variable of the predicate becomes a Normaliz
   * coordinate, so instead each ite is expanded into a disjunction over its
   * branches, guarded by its condition:
   *   (>= (ite c x y) 1) --> (or (and (>= x 1) c) (and (>= y 1) (not c)))
   *   (ite c p q)        --> (or (and p c) (and q (not c)))
   * An atom with k distinct ites yields up to 2^k disjuncts, each guarded by
   * the conditions of all of them:
   *   (>= (ite c1 x y) (ite c2 1 2))
   *   --> (or (and (>= x 1) c1 c2) (and (>= x 2) c1 (not c2))
   *           (and (>= y 1) (not c1) c2) (and (>= y 2) (not c1) (not c2)))
   *
   * The conversion is done by IteEliminationConverter, so the traversal is
   * iterative and the only kind it treats specially is ite.
   *
   * @param n a Boolean term without binders, e.g. a Boolean combination of
   * linear integer constraints whose integer terms may contain ite
   * @param e the environment, used for its node manager and rewriter
   * @param stats optional statistics collector, may be nullptr
   * @return an equivalent node without ite
   */
  static Node removeItes(Node n, Env& e, LiaStarStatistics* stats = nullptr);

  /**
   * Distribute conjunctions over disjunctions, turning a predicate in
   * negation normal form into DNF:
   *   (and (or a b) (or c d)) --> (or (and a c) (and b c) (and a d) (and b d))
   * The number of disjuncts is the product of the sizes of the disjunctions
   * and each disjunct later costs a cone computation. Partial conjunctions
   * are therefore checked with areAssertionsUnsat while the product is built,
   * and an unsat one is dropped together with all disjuncts it would have
   * produced. The result is still equivalent to n.
   *
   * Only and and or are distributed; every other term is an atom, e.g. a
   * constraint or a negated Boolean variable, see removeNot.
   *
   * @param n a node in negation normal form
   * @param e the environment, used for its node manager and options
   * @param stats optional statistics collector, may be nullptr
   * @param context conjuncts known to hold wherever n occurs: the atoms of
   * the enclosing conjunctions, passed down by the recursive calls. They only
   * strengthen the pruning checks and are not part of the result.
   * @return an equivalent node in DNF, which may be a single conjunction or
   * atom, or false if every disjunct was dropped. Disjunctions nested in
   * disjunctions are not flattened, see recursiveFlatten.
   */
  static Node distribute(Node n,
                         Env& e,
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
                                   Env& e,
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
                             Env& e,
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
   * Convert a LIA predicate in DNF into one constraint system per disjunct,
   * each a list of linear constraints a_1 x_1 + ... + a_n x_n ~ b with ~ in
   * {<, <=, =, >=, >} over the Normaliz coordinates x[1]..x[k] of
   * `variables`.
   *
   * The constraints are Normaliz symbolic constraint strings rather than
   * numeric matrices: libnormaliz::readNormalizInput parses them and does the
   * translation into Normaliz's internal matrices, see normalizCheckSat. The
   * string format is easier to debug, its cost is negligible compared to
   * computing the cone, and the input printed by trace tag
   * liastar-normalizCheckSat can be fed to the normaliz binary as is.
   *
   * @param variables a node of Kind BOUND_VAR_LIST; its i-th variable is the
   * Normaliz coordinate x[i + 1]
   * @param n a LIA predicate in DNF
   * @return one pair per disjunct of n: its constraints, e.g.
   * {"2x[1] - x[3] >= 5;", "x[2] = 0;"}, together with the disjunct itself
   */
  static std::vector<std::pair<std::vector<std::string>, Node>> getMatrices(
      Node variables, Node n);

  /**
   * Print, under trace tag liastar-ext-smt, an SMT-LIB query asserting that
   * a step changed the meaning of its input, e.g. a step of toDNF or the
   * reduction of a predicate to LIA in LiaStarExtension::checkFullEffort.
   * For the step "nnf" with before (not (>= x 1)) and after (< x 1) it prints
   *   (push 1)
   *   (echo "nnf")
   *   (assert
   *     (distinct
   *       (not (>= x 1))
   *       (< x 1)
   *     )
   *   )
   *   (check-sat)
   *   (pop 1)
   * The step preserved equivalence exactly when the query is unsat. The
   * declarations of the free variables are not printed, so after adding
   * them, e.g. (declare-const x Int), the traced output can be run with
   * cvc5 --incremental to find the step that broke it. Does nothing when
   * the trace tag is off.
   *
   * @param step the name of the step, echoed before its query
   * @param before the input of the step
   * @param after the output of the step
   */
  static void traceEquivalenceCheck(const char* step, Node before, Node after);

 private:
  /**
   * Convert a predicate to negation normal form and eliminate the negated
   * constraints that remain, since a Normaliz constraint cannot be negated.
   * The relation is flipped, e.g. (not (>= a b)) becomes (< a b), except
   * that a negated equality becomes the disjunction (or (> a b) (< a b));
   * this is why removeNot runs before distribute. A negated Boolean variable
   * has no relation to flip and is kept:
   *   (not (or p (>= x 1))) --> (and (not p) (< x 1))
   *
   * Both steps are iterative: TheoryBoolRewriter::computeNnfNorm computes
   * the negation normal form, and NegatedConstraintConverter flips the
   * negated constraints.
   *
   * @param n an ite-free Boolean combination of linear integer constraints
   * and Boolean variables
   * @param e the environment, used for its node manager
   * @return an equivalent node built from and, or, unnegated constraints and
   * possibly negated Boolean variables
   */
  static Node removeNot(Node n, Env& e);
  /**
   * Flatten a node and, one level down, each of its children by their own
   * kinds. expr::algorithm::flatten only merges nesting of the node's own
   * kind, so the alternating and/or structure left by distribute needs both
   * levels: (or (and a (and b c)) (or d e)) becomes (or (and a b c) d e).
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