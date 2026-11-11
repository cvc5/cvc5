/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Extension to the theory of arithmetic for the LIA* predicate
 * int.star-contains.
 */

#ifdef CVC5_USE_NORMALIZ

#ifndef CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H
#define CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H

#include <map>
#include <memory>
#include <unordered_set>
#include <vector>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "expr/node.h"
#include "libnormaliz/libnormaliz.h"
#include "smt/env_obj.h"
#include "smt/solver_engine.h"
#include "theory/arith/liastar/liastar_stats.h"
#include "theory/ext_theory.h"
#include "theory/theory.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

class InferenceManager;
class TheoryArith;

namespace liastar {

/**
 * The integer type used by Normaliz, as in liastar_utils.h. Note this shadows
 * cvc5::internal::Integer within namespace liastar.
 */
typedef mpz_class Integer;
/** A row of arithmetic terms, e.g. the monomials of one cone contribution. */
typedef std::vector<Node> Vector;

/**
 * The LIA* extension, for literals of the form
 *   (int.star-contains (lambda ((x_1 Int) ... (x_n Int)) p) y_1 ... y_n)
 * which state that y = (y_1, ..., y_n) is a sum of finitely many vectors of
 * S = {x | p(x)}, i.e. y is in the star S* of S (the empty sum is 0).
 *
 * Such a literal is reduced to linear integer arithmetic by a lemma:
 * 1. p is split into convex cells D_1, ..., D_m (the disjuncts of its DNF),
 *    so S is the union of the integer points of the polyhedra
 *    P_i = {x | D_i(x)}.
 * 2. Normaliz describes the integer points of each P_i as a finite union of
 *    linear sets g + H_i*N + M_i*Z, one per module generator g of P_i, where
 *    H_i is the Hilbert basis of the recession cone of P_i and M_i is a
 *    basis of its maximal subspace, which is empty unless P_i contains a
 *    line.
 * 3. The star of a linear set g + H*N + M*Z is
 *    {mu*g + H*l + M*m | mu >= 0, l >= 0, mu = 0 => (l = 0 and m = 0)}, and
 *    the star of a union is the sum of the stars. Fresh integer skolems for
 *    mu, l and m thus express y in S* in linear arithmetic.
 *
 * For example, S = {(x, y) | x >= 2 and y = 1} has the module generator
 * (2, 1) and the Hilbert basis {(1, 0)}, so the literal
 *   L = (int.star-contains (lambda ((x Int) (y Int)) (and (>= x 2) (= y 1)))
 *                          a b)
 * is reduced by the lemma
 *   (= L (and (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
 *             (= a (+ (* 2 mu) l)) (= b mu)))
 * Here the implication excludes (1, 0) = 0*(2, 1) + 1*(1, 0), which is not a
 * sum of vectors of S. See the file comment of liastar_extension.cpp for the
 * full picture, and
 * - Levatich, M., Bjorner, N., Piskac, R., Shoham, S. (2020).
 *   Solving LIA* Using Approximations.
 *   VMCAI 2020.
 *   https://doi.org/10.1007/978-3-030-39322-9_17
 *
 * Two strategies compute the cells (option arith-liastar-lazy):
 * - eager (`eagerCheckStar`): convert p to DNF, build a cone for every
 *   disjunct up front and send the exact equivalence (= L star) in one shot;
 * - lazy (`lazyCheckStar`, the default): the DNF can blow up, so instead a
 *   persistent incremental subsolver seeded with p enumerates the cells one
 *   refinement round at a time. The star built from the cells found so far
 *   under-approximates S*, so the equivalence is asserted only tentatively
 *   under a fresh boolean guard until the subsolver is unsat, i.e. every
 *   cell is covered, at which point the exact equivalence is sent.
 *
 * The skolems witness y in S* when L holds, but when L is false the lemma
 * only says that this one choice of them is not a witness. A negated L is
 * therefore also reduced, once the equivalence is exact, by the lemma
 *   (or L (forall ((mu Int) (l Int))
 *           (not (and (>= mu 0) (>= l 0) (=> (= mu 0) (= l 0))
 *                     (= a (+ (* 2 mu) l)) (= b mu)))))
 * which the quantifier instantiation for linear arithmetic handles. For
 * example, (not L) with a = 5 and b = 2 is unsat, since (5, 2) is
 * (2, 1) + (3, 1). In the lazy strategy a negative literal discovers one cell
 * per round, without the shortcuts of the positive case, until the
 * enumeration is complete; an under-approximation of S* cannot certify that
 * y is outside S*.
 *
 * The reduction requires p to be a Boolean combination of linear integer
 * constraints over x_1, ..., x_n. It throws a LogicException otherwise, e.g.
 * for (lambda ((x Int)) (= x (* 2 c))) with a constant c, whose set
 * depends on c.
 *
 * TheoryArith preregisters terms with preRegisterTerm, notifies the
 * extension of asserted literals with notifyAssertion, calls checkFullEffort
 * at full effort, once the linear solver has a model, and collectModelValues
 * when building the model.
 */
class LiaStarExtension : EnvObj
{
 public:
  /**
   * @param env the environment
   * @param containing the theory of arithmetic, whose facts are checked and
   * whose inference manager sends the lemmas
   */
  LiaStarExtension(Env& env, TheoryArith& containing);
  ~LiaStarExtension();

  /**
   * Register n with the extended theory if it is an int.star-contains term.
   *
   * @param n a term preregistered with the theory of arithmetic
   */
  void preRegisterTerm(TNode n);

  /**
   * Check the int.star-contains literals asserted to arithmetic, of either
   * polarity, and send lemmas for them. For a literal whose atom L has
   * lambda (lambda ((x_1 Int) ... (x_n Int)) p) and vector
   * y = (y_1, ..., y_n), where p(y) is p with x replaced by y, this
   * 1. with --arith-liastar-assume-nonnegative, sends
   *    (=> L (and (>= y_1 0) ... (>= y_n 0))),
   * 2. sends the split lemma (or p(y) (not p(y))), so the SAT solver decides
   *    p(y). If this call has sent any lemma so far, e.g. this one, the
   *    literal is left for a later call,
   * 3. with --arith-liastar-model-value (the default), stops for a positive
   *    literal if p(y), or the last star under-approximation computed for L
   *    by the lazy strategy, is true in arithModel, since then y is in S*,
   * 4. if the exact reduction of L was sent already, sends for a negative
   *    literal the lemma (or L (forall ...)) of the class documentation, once
   *    per atom, and stops,
   * 5. otherwise reduces L with the eager or the lazy strategy, see the class
   *    documentation.
   *
   * @param arithModel the model of the linear solver, which maps arithmetic
   * variables to constants, e.g. {a -> 3, b -> 1}
   * @param termSet the terms of the model, only traced
   */
  void checkFullEffort(std::map<Node, Node>& arithModel,
                       const std::set<Node>& termSet);

  /**
   * Notify the extension that a literal of the form (int.star-contains ...)
   * or (not (int.star-contains ...)) was asserted to arithmetic.
   */
  void notifyAssertion() { d_hasAssertions = true; }

  /**
   * Whether a literal of the form (int.star-contains ...) or
   * (not (int.star-contains ...)) was asserted in this context. Otherwise
   * TheoryArith calls neither checkFullEffort nor collectModelValues, so a
   * problem without such literals does not compute the model of the linear
   * solver for the extension.
   */
  bool hasAssertions() const { return d_hasAssertions; }

  /**
   * Assert each asserted int.star-contains literal to the model. The model
   * cannot evaluate an atom whose vector is in S* but not in S, e.g.
   *   (int.star-contains (lambda ((x Int)) (= x 2)) a)
   * with a = 4, so it takes the value of the literal, which the lemmas of
   * checkFullEffort guarantee.
   *
   * @param m the model
   * @return false if a literal could not be asserted to m
   */
  bool collectModelValues(TheoryModel* m);

 private:
  /**
   * Collect the facts asserted to arithmetic of the form
   * (int.star-contains ...) or (not (int.star-contains ...)).
   *
   * @param assertions the vector the literals are appended to
   */
  void getAssertions(std::vector<Node>& assertions);

  /**
   * Build the "sum constraints" that tie the star vector to the cone
   * contributions: for each coordinate i,
   *     vec[i] = sum over all generators of (point[i] + sum over rays of
   * ray[i]). `lambdas` holds one (point, rays) contribution per module
   * generator across all cones (as produced by
   * `LiaStarUtils::getGeneratorBody`); `vec` is the star vector (the v_1 ...
   * v_n). Returns the n equalities. For a polyhedron Normaliz appends a
   * homogenizing coordinate to each generator, e.g. the module generator 2 1 1
   * for (and (>= x 2) (= y 1)); the sums ignore it.
   */
  static std::vector<Node> buildSumConstraints(
      NodeManager* nm,
      Node zero,
      const std::vector<Node>& vec,
      const std::vector<std::pair<Vector, std::vector<Vector>>>& lambdas);

  /**
   * Trace the cone's Hilbert basis and return its module generators -- the base
   * lattice points g of the decomposition { g + sum_j l_j h_j } of the cone's
   * integer points. A purely homogeneous cone, e.g. the one of
   * (and (>= x y) (>= y 0)), has no module generators; its single base point is
   * then the origin, so the zero vector is returned instead.
   */
  static std::vector<std::vector<Integer>> getConeGenerators(
      libnormaliz::Cone<Integer>& cone, size_t dimension);

  /**
   * Emit the preamble of a self-contained SMT-LIB script on the
   * "liastar-ext-smt" channel: solver options plus a declaration for every star
   * variable in `variables`, and a non-negativity assertion for each of them
   * when `assumeNonnegative`, since Normaliz only assumes them to be
   * nonnegative with --arith-liastar-assume-nonnegative. The queries later
   * emitted on the same channel (see `LiaStarUtils::traceEquivalenceCheck`)
   * then form a replayable soundness check of the reduction: every (check-sat)
   * must answer unsat.
   */
  static void traceSmtPreamble(Node variables, bool assumeNonnegative);

  /**
   * Emit, on the "liastar-ext-smt" channel, the queries validating the
   * membership encoding: one query per disjunct asserting it differs from the
   * predicate cell it encodes, and a final query asserting the whole predicate
   * (lambda[1]) differs from the disjunction of all membership formulas. All of
   * them must be unsat when the trace is replayed.
   */
  static void traceMembershipValidation(
      NodeManager* nm,
      Node lambda,
      const std::vector<std::pair<Node, Node>>& lia);

  /**
   * Convert the body p of a lambda into one Normaliz constraint system per
   * disjunct of its DNF, see LiaStarUtils::toDNF and LiaStarUtils::getMatrices.
   * For example, the lambda
   *   (lambda ((x Int) (y Int)) (or (and (>= x 2) (= y 1)) (>= y 3)))
   * yields the pairs
   *   {"x[1] >= 2;", "x[2] = 1;"} with (and (>= x 2) (= y 1))
   *   {"x[2] >= 3;"} with (>= y 3)
   *
   * @param n a lambda (lambda ((x_1 Int) ... (x_n Int)) p) with p in LIA
   * @return one pair per disjunct: its constraints over the Normaliz
   * coordinates x[1]..x[n], together with the disjunct itself
   * @throws LogicException if p is not a Boolean combination of linear
   * integer constraints over x_1, ..., x_n, e.g. if it captures a constant,
   * see LiaStarUtils::getMatrices
   */
  const std::vector<std::pair<std::vector<std::string>, Node>>
  convertQFLIAToMatrices(Node n);

  /**
   * Eager path: build a Normaliz cone for every DNF disjunct of the predicate
   * and accumulate the star constraints over all of them, see steps 2 and 3
   * of the class documentation. Empty (infeasible) cones are skipped.
   *
   * @param n the int.star-contains atom; its children after the lambda are
   *   the vector y
   * @param pairs one (constraint rows, disjunct node) pair per disjunct, as
   *   returned by `convertQFLIAToMatrices`
   * @param skolems the vector the fresh multiplier skolems are appended to
   * @return the non-empty cones, each paired with the disjunct it came from
   *   (used by `getMembershipDisjuncts` for the debug trace), and the star
   *   constraints: the side constraints of the fresh multipliers plus the
   *   sum constraints tying y to the cones' contributions. Their conjunction
   *   is equivalent to `y in S*`.
   */
  std::pair<std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>,
            std::vector<Node>>
  getCones(Node n,
           const std::vector<std::pair<std::vector<std::string>, Node>>& pairs,
           std::vector<Node>& skolems);

  /**
   * Lazy path: build the cone for a single disjunct and append it to the list
   * of cones for `lambda` stored in `d_lazyCones`. If the cone is empty (the
   * disjunct is infeasible) it is not added.
   *
   * @param lambda the lambda of the int.star-contains atom
   * @param pair the disjunct's constraint rows and node, as returned by
   *   `LiaStarUtils::getMatrix`
   */
  void addCone(Node lambda,
               const std::pair<std::vector<std::string>, Node>& pair);

  /**
   * Lazy path: return the star constraints of `atom` over all cones
   * accumulated so far in `d_lazyCones[lambda]` (the cones added by previous
   * calls to `addCone`).
   *
   * The per-cone constraints (and their fresh skolems) are computed only for
   * cones that have not been processed in a previous call and are accumulated
   * in `d_starConstraints[atom]`, so the skolems stay stable across
   * refinement rounds; the sum constraints, which span all cones, are rebuilt
   * from the accumulated `d_lambdas[atom]` on each call. The skolems are
   * recorded in `d_literalSkolems[atom]`.
   */
  std::vector<Node> getStarConstraints(Node atom, Node lambda);

  /**
   * Debug helper, used only for the "liastar-ext-smt" trace. Builds the
   * *membership* encoding `y in S`: one existentially quantified formula per
   * (cone, module generator) stating that y is the single element
   * `g + sum_j l_j h_j` of that cone. The disjunction of all returned
   * formulas is equivalent to the predicate itself, which the emitted trace
   * queries let an external solver verify.
   *
   * @param n the lambda
   * @param cones the cones with their originating disjuncts, as returned by
   *   `getCones`
   * @return each membership formula paired with the disjunct it encodes
   */
  std::vector<std::pair<Node, Node>> getMembershipDisjuncts(
      Node n, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>& cones);

  /**
   * Performs the eager Hilbert-basis reduction for a single int.star-contains
   * atom: sends the exact reduction lemma (= atom star), with star the
   * conjunction of the star constraints derived from the cones of `lambda`,
   * and records it with `recordReduction`.
   *
   * @param atom the int.star-contains atom
   * @param lambda the lambda of `atom`, see uf::FunctionConst::getDefinition
   * @param polarity whether the literal asserting `atom` is positive
   */
  void eagerCheckStar(Node atom, Node lambda, bool polarity);

  /**
   * Performs one round of the lazy Hilbert-basis reduction for a single
   * int.star-contains atom: refines the lambda's subsolver with the negations
   * of the cone-disjuncts discovered since the previous round, then delegates
   * to `lazyHilbert`. If the enumeration of the lambda's cells is complete
   * already (through an earlier round, possibly of another literal or in
   * another user context) the exact reduction is sent right away.
   *
   * A negative literal only needs the enumeration to complete.
   *
   * @param atom the int.star-contains atom
   * @param lambda the lambda of `atom`
   * @param polarity whether the literal asserting `atom` is positive
   */
  void lazyCheckStar(Node atom, Node lambda, bool polarity);

  /**
   * A persistent, incremental subsolver dedicated to one lambda (one
   * int.star-contains predicate). It is used to enumerate the convex cells of
   * the predicate's satisfying region: it is seeded once with the
   * (nonnegative) predicate and then refined across rounds with the
   * negations of the discovered cone-disjuncts, one assertion per disjunct;
   * see `lazyCheckStar`.
   */
  struct Subsolver
  {
    /** the incremental QF_LIA subsolver. */
    std::unique_ptr<SolverEngine> engine;
    /** the lambda's bound variables ... */
    std::vector<Node> from;
    /** ... and the fresh skolem constants substituted for them, since a
     * subsolver cannot be given a formula with free (bound) variables. */
    std::vector<Node> to;
    /**
     * The (nonnegative) predicate in skolem space. It is already asserted in
     * `engine`; it is kept only to read off the predicate's atoms when
     * building a disjunct from the model.
     */
    Node base;
    /** number of cones in `d_lazyCones[lambda]` already negated in `engine` */
    size_t negated = 0;
  };

  /**
   * Returns the subsolver for `lambda`, creating and seeding it (with the
   * nonnegative predicate) on first use.
   */
  Subsolver& getSubsolver(Node lambda);

  /**
   * One lazy refinement round for `atom`: ask the subsolver for a model in
   * a region of the predicate not yet covered by a cone, read off the convex
   * cell containing it (`LiaStarUtils::getDisjunct`), and hand it to
   * `processDisjunct`.
   */
  void lazyHilbert(Node atom, Node lambda, Subsolver& sub, bool polarity);

  /**
   * Tail of one lazy refinement round: turn `disjunct` -- a freshly discovered
   * cell of the predicate, in bound-variable space -- into a cone, rebuild
   * the star constraints over all cones found so far, and emit the reduction
   * lemma: guarded by a fresh boolean while the star is still an
   * under-approximation (`complete` false), unconditional once every cell is
   * covered (`complete` true, `disjunct` is then the false constraint). In
   * the latter case the exact reduction is recorded with `recordReduction`.
   */
  void processDisjunct(
      Node atom, Node lambda, Node disjunct, bool complete, bool polarity);

  /**
   * Record that the exact reduction lemma (= atom star) was sent in this user
   * context, and send the lemma for the negated atom if the literal is
   * negative, see sendNegatedReduction. The formula
   * (forall ((mu Int) ...) (not star)) that holds when the atom is false is
   * built by replacing `skolems` in `star` with bound variables; it is null,
   * and the negated lemma is not needed, if `star` has no skolems, as the
   * reduction is then exact on its own.
   *
   * @param atom the int.star-contains atom
   * @param star the constraints the atom was equated with
   * @param skolems the skolems of `star`
   * @param polarity whether the literal asserting `atom` is positive
   */
  void recordReduction(Node atom,
                       Node star,
                       const std::vector<Node>& skolems,
                       bool polarity);

  /**
   * Send the reduction lemma (or atom (forall ((mu Int) ...) (not C))) of a
   * negated atom, stored in d_negatedReductions, see recordReduction. Does
   * nothing if C has no skolems, as the reduction lemma (= atom C) is then
   * exact.
   *
   * @param atom an int.star-contains atom that is asserted false
   * @throws LogicException if the lemma is needed but the logic has no
   * quantifiers
   */
  void sendNegatedReduction(Node atom);

  /** node manager */
  NodeManager* d_nm;
  /** commonly used terms */
  Node d_true;
  Node d_false;
  Node d_zero;
  Node d_one;
  /** The theory of arithmetic, whose asserted facts getAssertions reads */
  TheoryArith& d_arith;
  /** A reference to the arithmetic state object, for its valuation. */
  TheoryState& d_astate;
  /** The inference manager of TheoryArith, used to send lemmas. */
  InferenceManager& d_im;
  /** Callback for the extended theory below. */
  ExtTheoryCallback d_extTheoryCb;
  /** Extended theory, with which the int.star-contains terms are registered */
  ExtTheory d_extTheory;
  /** Whether an int.star-contains literal was asserted in this context */
  context::CDO<bool> d_hasAssertions;
  /**
   * Maps each atom whose exact reduction lemma was sent to the formula
   * (forall ((mu Int) ...) (not C)) that holds when the atom is false, or to
   * null if C has no skolems, see recordReduction. User-context dependent,
   * like the lemmas: after a user pop the exact reduction is sent again. No
   * further lazy refinement rounds run for these atoms.
   */
  context::CDHashMap<Node, Node> d_negatedReductions;
  /** The atoms whose negated reduction lemma was sent, user-context dependent
   */
  context::CDHashSet<Node> d_negatedReductionsSent;
  /** Statistics for the liastar extension */
  LiaStarStatistics d_stats;

  /**
   * The cones accumulated so far during the lazy Hilbert-basis reduction,
   * keyed by lambda. Each call to `addCone` appends the cone for the current
   * disjunct, and `getStarConstraints` computes the starLia constraints for
   * the newly added cones, accumulating them across calls. The cones depend
   * only on the predicate, so like the state below they are not
   * context-dependent: they stay valid in every user context.
   */
  std::map<Node, std::vector<std::pair<Node, libnormaliz::Cone<Integer>>>>
      d_lazyCones;

  /**
   * The lambdas whose cell enumeration is complete: every cell of the
   * predicate has a cone in `d_lazyCones`, so the star constraints over
   * these cones are exact.
   */
  std::unordered_set<Node> d_completeLambdas;

  /**
   * The per-cone starLia constraints computed so far for each
   * int.star-contains atom (the atom, not its lambda: atoms over one lambda
   * share the cone list but must not share the multiplier skolems, or their
   * sum constraints would force their vectors equal).
   * `getStarConstraints` only generates the skolems and constraints
   * for cones in `d_lazyCones` that have not been processed yet, appending
   * them here, so previously computed constraints (and their skolems) are
   * reused across refinement rounds. These are the constraints that are
   * independent of the other cones (the (>= mu 0), (>= l 0), and
   * (=> (= mu 0) (= l 0)) constraints); the sum constraints span all cones
   * and are rebuilt each call.
   */
  std::map<Node, std::vector<Node>> d_starConstraints;
  /**
   * The (point, rays) contributions computed so far for each atom,
   * kept in step with `d_starConstraints`. They are used to rebuild the sum
   * constraints over all cones on each call to `getStarConstraints`.
   */
  std::map<Node, std::vector<std::pair<Vector, std::vector<Vector>>>> d_lambdas;
  /** The number of cones in `d_lazyCones[lambda]` already processed, per
   * atom: each atom builds its own multipliers over the shared list. */
  std::map<Node, size_t> d_processedCones;
  /**
   * The skolems created for the star constraints of each atom (the
   * multipliers), in creation order. They are the bound variables of the
   * negated reduction lemma, see recordReduction.
   */
  std::map<Node, std::vector<Node>> d_literalSkolems;

  /**
   * The last starLia under-approximation (`star`) computed for each
   * int.star-contains atom by `processDisjunct`. The model-value check in
   * `checkFullEffort` uses it to skip refinement when the current model
   * already satisfies the predicate or this under-approximation.
   */
  std::map<Node, Node> d_lastStarLia;

  /**
   * The fresh boolean guard of the last (still active) tentative reduction
   * `g => (atom = star)` emitted for each int.star-contains atom by
   * `processDisjunct`, or null once the exact reduction was sent. When a
   * later round produces a larger under-approximation, the previous guard is
   * deactivated (we assert `(not g)`), so at most one tentative reduction is
   * active per atom. User-context dependent, like the tentative lemma.
   */
  context::CDHashMap<Node, Node> d_lastGuard;

  /**
   * The incremental subsolver for each lambda (int.star-contains predicate).
   * Each is created lazily and persists for the lifetime of the extension, so
   * the predicate's cells are enumerated incrementally across refinement
   * rounds.
   */
  std::map<Node, Subsolver> d_subsolvers;

}; /* class LiaStarExtension */

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR_EXTENSION_H */

#endif /* CVC5_USE_NORMALIZ */
