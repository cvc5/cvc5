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

#include <unordered_set>

#include "expr/node.h"
#include "expr/node_converter.h"
#include "libnormaliz/libnormaliz.h"
#include "smt/env.h"
#include "theory/arith/liastar/liastar_stats.h"
#include "theory/arith/linear/normal_form.h"
#include "util/result.h"

namespace cvc5::internal {

class SolverEngine;

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
 * Expands the Boolean equalities and xors of a predicate into and, or and
 * not, since TheoryBoolRewriter::computeNnfNorm keeps them as connectives
 * and getMatrices has no constraint for them:
 *   (= p q)   --> (or (and p q) (and (not p) (not q)))
 *   (xor p q) --> (or (and p (not q)) (and (not p) q))
 * For example, (= (>= x 1) (<= x 2)), which holds for x in {1, 2}, becomes
 *   (or (and (>= x 1) (<= x 2)) (and (not (>= x 1)) (not (<= x 2))))
 * The disjunctive forms suit the DNF that LiaStarUtils::toDNF builds. Used
 * by LiaStarUtils::removeNot.
 */
class BooleanEqualityConverter : public NodeConverter
{
 public:
  BooleanEqualityConverter(NodeManager* nm);
  /**
   * @param n a term whose children are already converted
   * @return the expansion of n if n is an equality of Booleans or a xor,
   * otherwise n itself
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
 * Utilities shared by the liastar extension (see liastar_extension.cpp for
 * the overall decision procedure). They fall into three groups:
 *
 * 1. Predicate normalization (`removeItesAndNots`, `toDNF` and their
 *    workers): turn the body of a star lambda into a flat disjunction of
 *    conjunctions of unnegated linear (in)equalities, the only shape that can
 *    be rendered as polyhedral cones.
 *
 * 2. The Normaliz bridge (`getMatrix`, `getMatrices`, `buildCone`,
 *    `isEmptyCone`, `getGeneratorBody`): render conjunctions as Normaliz
 *    "symbolic" constraint strings, compute cones (Hilbert basis and module
 *    generators), decide satisfiability of candidate disjuncts, and encode a
 *    module generator back into arithmetic.
 *
 * 3. Model extraction for the lazy strategy (`getDisjunct`, `collectAtoms`):
 *    read a model from an incremental subsolver and distil the convex cell
 *    of the predicate containing it.
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
   * The first child may also be a function array constant, e.g. for
   * (lambda ((x Int)) (= x 5)), or with --no-uf-lazy-ll the skolem of the
   * lifted lambda; both are resolved, see uf::FunctionConst::getDefinition.
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
   * The steps are removeItesAndNots (removeItes and removeNot) and
   * distribute, followed by flattening; no new variables are introduced.
   *
   * @param n a Boolean combination (and, or, not, =>, ite, and = and xor of
   * Booleans) of linear integer constraints (<, <=, =, >=, >) and Boolean
   * variables, whose integer terms may contain ite
   * @param e the environment, used for its node manager, rewriter and options
   * @param stats optional statistics collector, may be nullptr
   * @return an equivalent node in DNF: a disjunction of conjunctions of
   * atoms, or a single conjunction or atom, without ite and with negation
   * only on Boolean variables. Disjuncts the subsolver shows to be unsat
   * are dropped, see distribute.
   */
  static Node toDNF(Node n, Env& e, LiaStarStatistics* stats = nullptr);

  /**
   * Eliminate ite and negated constraints from a LIA predicate: the first two
   * steps of toDNF, see removeItes and removeNot. The lazy strategy uses this
   * form to seed its subsolvers and to normalize the cells it reads from
   * their models, which must be conjunctions of unnegated constraints before
   * getMatrix renders them.
   *
   * @param n a Boolean combination (and, or, not, =>, ite, and = and xor of
   * Booleans) of linear integer constraints and Boolean variables, whose
   * integer terms may contain ite
   * @param e the environment, used for its node manager and rewriter
   * @param stats optional statistics collector, may be nullptr
   * @return an equivalent node built from and, or, unnegated constraints and
   * possibly negated Boolean variables, without ite
   */
  static Node removeItesAndNots(Node n,
                                Env& e,
                                LiaStarStatistics* stats = nullptr);

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
   * Only genuine bound variables are quantified; free constants among
   * `freeVariables` are left in place, since checking a formula with free
   * constants is equivalent to checking its existential closure. The lazy
   * strategy checks formulas over the skolem constants of its subsolvers this
   * way.
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
   * exactly when the resulting inhomogeneous cone has no integer points, see
   * isEmptyCone.
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
   * Convert a single disjunct of a LIA predicate in DNF, i.e. one convex
   * cell, into a constraint system: a list of linear constraints
   * a_1 x_1 + ... + a_n x_n ~ b with ~ in {<, <=, =, >=, >} over the Normaliz
   * coordinates x[1]..x[k] of `variables`.
   *
   * The constraints are Normaliz symbolic constraint strings rather than
   * numeric matrices: libnormaliz::readNormalizInput parses them and does the
   * translation into Normaliz's internal matrices, see buildCone. The string
   * format is easier to debug, its cost is negligible compared to computing
   * the cone, and the input printed by trace tag liastar-ext can be fed to
   * the normaliz binary as is.
   *
   * @param variables a node of Kind BOUND_VAR_LIST; its i-th variable is the
   * Normaliz coordinate x[i + 1]
   * @param n a linear constraint, a conjunction of linear constraints, or a
   * Boolean constant (encoded as the tautology "x[1] = x[1];" or the
   * contradiction "1 = 0;", since Normaliz needs at least one constraint)
   * @return the constraints of n, e.g. {"2x[1] - x[3] >= 5;", "x[2] = 0;"},
   * together with n itself
   * @throws LogicException if an atom of n is not a linear integer
   * constraint over `variables`, e.g. a Boolean variable p, an equality of
   * Booleans (= p (>= x 1)), which toDNF expands, an equality of other
   * non-arithmetic terms (= b #x00), or (= x (* 2 a)) for a term a that is
   * not in `variables`, see getString
   */
  static std::pair<std::vector<std::string>, Node> getMatrix(Node variables,
                                                             Node n);

  /**
   * Convert a LIA predicate in DNF into one constraint system per disjunct,
   * by applying getMatrix to each disjunct of a disjunction, or to the
   * predicate itself if it is a single conjunction or atom.
   *
   * @param variables a node of Kind BOUND_VAR_LIST; its i-th variable is the
   * Normaliz coordinate x[i + 1]
   * @param n a LIA predicate in DNF
   * @return one pair per disjunct of n: its constraints, e.g.
   * {"2x[1] - x[3] >= 5;", "x[2] = 0;"}, together with the disjunct itself
   * @throws LogicException as getMatrix
   */
  static std::vector<std::pair<std::vector<std::string>, Node>> getMatrices(
      Node variables, Node n);

  /**
   * Build the Normaliz cone of a single convex polyhedron and compute its
   * Hilbert basis, module generators and maximal subspace. This is the one
   * place that constructs a libnormaliz cone.
   *
   * @param dimension the ambient dimension (the number of star variables; the
   * Normaliz "amb_space")
   * @param constraints the rows of the cone, one symbolic constraint each,
   * as produced by getMatrix
   * @param assumeNonnegative whether to restrict the cone to the nonnegative
   * orthant (the arith-liastar-assume-nonnegative option); when false every
   * coordinate is sign-unrestricted, since int.star-contains does not itself
   * constrain the sign of the summands: the lambda under the star does
   * @param stats optional statistics collector, may be nullptr
   * @return the computed cone
   */
  static libnormaliz::Cone<Integer> buildCone(
      size_t dimension,
      const std::vector<std::string>& constraints,
      bool assumeNonnegative,
      LiaStarStatistics* stats = nullptr);

  /**
   * Whether a cone computed by buildCone has no integer points. A polyhedron
   * has integer points exactly when it has module generators; its affine
   * dimension does not tell, since (and (= x (* 2 z)) (= x (+ (* 2 w) 1)))
   * has rational points but no integer points. A homogeneous cone always
   * contains the origin.
   *
   * @param cone a cone computed by buildCone
   * @return true if `cone` has no integer points
   */
  static bool isEmptyCone(libnormaliz::Cone<Integer>& cone);

  /**
   * Normaliz's getHilbertBasis() only covers the pointed part of a cone: for
   * a cone containing a line, e.g. the one of (= (+ x y) 2) whose maximal
   * subspace is spanned by (1, -1), the nonnegative combinations of its
   * Hilbert basis miss lattice points. The basis of the maximal subspace is
   * appended to complete it. A direction of the maximal subspace can be used
   * both ways, so its multiplier is unrestricted in sign. Appending m and -m
   * instead would also be correct, but gives every point infinitely many
   * representations, which the arithmetic search then has to enumerate.
   *
   * @param cone a cone whose HilbertBasis and MaximalSubspace are computed
   * @param numPointed set to the number of leading vectors that come from
   * getHilbertBasis() and so take nonnegative multipliers
   * @return the Hilbert basis followed by the basis of the maximal subspace,
   * which is just the Hilbert basis for a pointed cone
   */
  static std::vector<std::vector<Integer>> getHilbertBasisWithLineality(
      libnormaliz::Cone<Integer>& cone, size_t& numPointed);

  /**
   * Check the incremental subsolver `smte` (which must already have the
   * membership predicate, and the negations of any previously discovered
   * cone-disjuncts, asserted) and read its model to build one disjunct (cell)
   * of the predicate's satisfying region: a conjunction that fixes every atom
   * of `assertion` to its model truth value (splitting a false integer
   * equality into the strict inequality the model satisfies).
   *
   * @param assertion the (skolem-space) predicate, used only to enumerate the
   * atoms read from the model; it is not asserted here
   * @param from the lambda's bound variables
   * @param to the skolem constants substituted for them; the returned
   * disjunct is mapped back from `to` to `from` (bound-variable space)
   * @param e the environment, used for its node manager and options
   * @param smte the incremental subsolver to check
   * @return the disjunct, `false` if `smte` is unsat (the predicate is fully
   * covered), or `true` if it has no atoms
   */
  static Node getDisjunct(Node assertion,
                          const std::vector<Node>& from,
                          const std::vector<Node>& to,
                          Env& e,
                          SolverEngine* smte);

  /**
   * Build the encoding of one module generator of a cone in terms of fresh
   * variables. The body is shared between the membership encoding
   * (`LiaStarExtension::getMembershipDisjuncts`, which existentially binds
   * `vars`) and the star encoding (`LiaStarExtension::getCones` /
   * `getStarConstraints`, which assert the constraints at the top level).
   *
   * @param dimension the ambient dimension of the cone
   * @param generator a module generator of the cone (a lattice point), or
   * the zero vector for a homogeneous cone
   * @param cone the cone, whose Hilbert basis and maximal subspace are the
   * rays, see getHilbertBasisWithLineality
   * @param star whether to build the star encoding (introduce a multiplier
   * `mu` for `generator` and couple the rays to it) or the plain membership
   * encoding (use `generator` as a fixed offset, with multiplier 1)
   * @param useSkolems whether the introduced variables are skolems (asserted
   * at the top level) or bound variables (to be existentially bound)
   * @param nm the node manager
   * @param vars output: the fresh variables introduced (the multiplier `mu`
   * and the ray multipliers `l_j`)
   * @param constraints output: the side constraints over `vars`
   * (non-negativity and, for the star encoding, the coupling constraints)
   * @param point output: the point `mu * generator` (star) or `generator`
   * @param rays output: the rays `l_j * h_j`, one per vector h_j of the
   * Hilbert basis and the maximal subspace
   */
  static void getGeneratorBody(size_t dimension,
                               const std::vector<Integer>& generator,
                               libnormaliz::Cone<Integer>& cone,
                               bool star,
                               bool useSkolems,
                               NodeManager* nm,
                               std::vector<Node>& vars,
                               std::vector<Node>& constraints,
                               std::vector<Node>& point,
                               std::vector<std::vector<Node>>& rays);

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

  /**
   * Collect the atomic predicates (leaves of the Boolean structure) of `n`
   * into `atoms`, in deterministic traversal order, using `visited` to avoid
   * duplicates.
   */
  static void collectAtoms(Node n,
                           std::vector<Node>& atoms,
                           std::unordered_set<Node>& visited);

 private:
  /**
   * Convert a predicate to negation normal form and eliminate the negated
   * constraints that remain, since a Normaliz constraint cannot be negated.
   * The relation is flipped, e.g. (not (>= a b)) becomes (< a b), except
   * that a negated equality becomes the disjunction (or (> a b) (< a b));
   * this is why removeNot runs before distribute. A negated Boolean variable
   * has no relation to flip and is kept:
   *   (not (or p (>= x 1))) --> (and (not p) (< x 1))
   * Equalities of Booleans and xors, which the negation normal form keeps,
   * are expanded first:
   *   (= p (>= x 1)) --> (or (and p (>= x 1)) (and (not p) (< x 1)))
   *
   * All three steps are iterative: BooleanEqualityConverter expands the
   * equalities and xors, TheoryBoolRewriter::computeNnfNorm computes the
   * negation normal form, and NegatedConstraintConverter flips the negated
   * constraints.
   *
   * @param n an ite-free Boolean combination (and, or, not, =>, and = and
   * xor of Booleans) of linear integer constraints and Boolean variables
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
   * order
   * @param p a linear polynomial, which is integral if its variables are in
   * `variables`
   * @return the polynomial as a string, e.g. "2x[1] - x[3] + 5"
   * @throws LogicException if a monomial of p is neither a constant nor a
   * multiple of a variable in `variables`, e.g. (* 2 a) for a constant a
   * captured by a lambda, (* x y), (mod x 2), or a term of another type, as
   * r in (>= x r) for a real r
   */
  static std::string getString(Node variables, linear::Polynomial& p);
};
}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__LIASTAR__UTILS_H */

#endif /* CVC5_USE_NORMALIZ */
