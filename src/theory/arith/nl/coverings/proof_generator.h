/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements the proof generator for coverings.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__NL__COVERINGS__PROOF_GENERATOR_H
#define CVC5__THEORY__ARITH__NL__COVERINGS__PROOF_GENERATOR_H

#ifdef CVC5_POLY_IMP

#include <poly/polyxx.h>

#include <map>
#include <vector>

#include "expr/node.h"
#include "proof/lazy_tree_proof_generator.h"
#include "proof/proof.h"
#include "proof/proof_set.h"
#include "smt/env_obj.h"
#include "theory/arith/nl/coverings/cdcac_utils.h"

namespace cvc5::internal {

class ProofGenerator;
class CDProof;

namespace theory {
namespace arith {
namespace nl {

struct VariableMapper;

namespace coverings {

struct RootMap
{
  /* All distinct roots of all constraint polynomials, sorted ascending,
   * with exactly one poly::Value per distinct real number. */
  std::vector<poly::Value> d_roots;

  // For each constraint polynomial, the indices into d_roots of its own roots,
  // sorted ascending.
  std::vector<std::pair<poly::Polynomial, std::vector<size_t>>> d_members;

  std::vector<size_t> polyRootIndices(const poly::Polynomial& p);
  size_t rootIndex(const poly::Value& r);
};

struct ProofInterval
{
  poly::Interval d_interval;
  poly::Polynomial d_poly;  // oriented like d_origin, see orientLikeConstraint
  Node d_origin;  // the original constraint on `d_poly` that is violated in
                  // `d_interval`
  // The expression stating that `d_poly` is `SGN_INV` in `d_interval` or
  // `IS_ROOT(p, r)`, if `d_interval` is a point interval at `r`.
  Node d_fact;
  Node d_elim;  // conclusion of SGN_INV_ELIM (open piece) / RAN_EVAL (point)

  ProofInterval(const poly::Interval& _d_interval,
                const poly::Polynomial& _d_poly,
                const Node& _d_origin,
                const Node& _d_fact)
      : d_interval(_d_interval),
        d_poly(_d_poly),
        d_origin(_d_origin),
        d_fact(_d_fact)
  {
  }
};

/**
 * The polynomial of constraint n, oriented like n itself. For n of the form
 * (k a b) or (not (k a b)), as_poly_constraint returns +-c*(a - b) with c > 0,
 * negating whenever the resulting sign condition would otherwise be > or >=.
 * This undoes that negation, returning q = c*(a - b), so that the canonical
 * literal (k q 0) has the same relation kind as n and can be derived from n
 * by ARITH_POLY_NORM_REL (which does not flip relations).
 */
poly::Polynomial orientLikeConstraint(const Node& n, const poly::Polynomial& p);

/* Builds the canonical root map from the raw pairs collected by
 * addUnivRoots(). */
RootMap buildRootMap(
    const std::vector<std::pair<poly::Polynomial, poly::Value>>& polyRoots);

/** Streams the map: canonical roots with ids, then membership. */
std::ostream& operator<<(std::ostream& os, const RootMap& rootMap);

/**
 * This class manages the proof creation during a run of the coverings solver.
 *
 * Though it implements the ProofGenerator interface getProofFor(Node), it only
 * gives a proof for a single node.
 *
 * It uses a LazyTreeProofGenerator internally to manage the tree-based proof
 * construction.
 */
class CoveringsProofGenerator : protected EnvObj
{
 public:
  friend std::ostream& operator<<(std::ostream& os,
                                  const CoveringsProofGenerator& proof);
  CoveringsProofGenerator(Env& env, context::Context* ctx);

  /** Start a new proof in this proof generator */
  void startNewProof(bool isUniv);
  /** Start a new recursive call */
  void startRecursive();
  /** Finish the current recursive call */
  void endRecursive(size_t intervalId);
  /** Start a new scope, corresponding to a guess in CDCAC */
  void startScope();
  /** Finish a scope and add the (generalized) sample that was refuted */
  void endScope(const std::vector<Node>& args);
  /** Return the current proof generator */
  ProofGenerator* getProofGenerator() const;
  CDProof* getUnivProofGenerator() const;

  void initializeRootMap();

  /**
   * Starts collecting the roots and intervals of var, discarding those
   * collected for a previous variable. Only the data of the last variable is
   * kept: when the coverings solver finds a conflict and every polynomial is
   * univariate, this is the variable whose constraints alone are unsat.
   */
  void startUnivVariable(const Node& var);

  /**
   * Calls LazyTreeProofGenerator::pruneChildren(f), but decorates the
   * predicate such that f only accepts the index.
   * @param f A Callable bool(std::size_t)
   */
  template <typename F>
  void pruneChildren(F&& f)
  {
    d_current->pruneChildren([&f](const detail::TreeProofNode& tpn) {
      // The direct children of recursive rules are scopes, but the ids are
      // attached to their children
      if (tpn.d_rule == ProofRule::SCOPE && tpn.d_children.size() == 1)
      {
        return f(tpn.d_children[0].d_objectId);
      }
      return f(tpn.d_objectId);
    });
  }
  void sortAndEraseDupsRoots();
  void addUnivRoots(const std::vector<poly::Value>& roots,
                    poly::Polynomial polys);
  void addPointPiece(const poly::Value& v,
                     const poly::Polynomial& p,
                     const Node& origin);

  // Adds `intervals` to `d_intervals`, breaking closed intervals and intervals
  // whose corresponding polynomial contains a root in the middle of it.
  void addIntervals(const std::vector<CACInterval>& intervals,
                    const std::map<Node, poly::Polynomial>& constraintPolys);

  // Refines the algebraic numbers of `d_rootMap` until all isolating intervals
  // are strictly separated from each other and from the rational roots, and
  // gives every endpoint in `d_intervals` the representation of its number
  // there, so that all steps of the proof agree on it. The checker compares
  // endpoints through their isolating intervals.
  void normalizeEndpoints();
  Node addCoverStep(const Node& var);

  // For each piece in `d_intervals`, adds the step introducing its fact:
  // IS_ROOT_INTRO(p, r, sturmTarski(r)) for a point piece, and
  // SGN_INV_INTRO(p, l, r, lo, hi, sturm(p), sturmTarski(l), sturmTarski(r))
  // for an open piece, where `(lo, hi)` is a rational window around `(l, r)`
  // that contains no root of `p` other than `l` and `r` (see `windowBelow` /
  // `windowAbove`).
  void addIntroSteps(const Node& var, VariableMapper& vm);

  // A rational strictly below (resp. above) the root `v` of `p` such that `p`
  // has no root in between: the lower (resp. upper) bound of the isolating
  // interval when `v` is algebraic; for a rational `v`, the midpoint between
  // `v` and the previous (resp. next) root of `p`, or `v - 1` (resp. `v + 1`)
  // when there is none. An infinite `v` is returned as is.
  Node windowBelow(const poly::Value& v, const poly::Polynomial& p);
  Node windowAbove(const poly::Value& v, const poly::Polynomial& p);

  void addElimSteps(const Node& var, VariableMapper& vm);

  void addResolutionStep(const Node& coverConc);

  /**
   * Derives the canonical literal of the constraint origin, which has the
   * form (k a b) or (not (k a b)), from origin itself. The literal is
   * (k q 0), respectively (not (k q 0)), where q is the cvc5 term of the
   * polynomial of origin (oriented like origin, see orientLikeConstraint).
   * Adds the steps
   *   ARITH_POLY_NORM      (= (* cx (- a b)) (* cy (- q 0)))
   *   ARITH_POLY_NORM_REL  (= (k a b) (k q 0))
   *   CONG                 (= (not (k a b)) (not (k q 0)))   [if negated]
   *   EQ_RESOLVE           literal                            [from origin]
   * and returns the literal. If origin already is the literal, no step is
   * added.
   */
  Node addNormalizedLiteral(const Node& origin, const Node& q);

  void closeUnivProof(std::vector<Node> constraints, VariableMapper& vm);
  /**
   * Add a direct interval conflict as generated in getUnsatIntervals().
   * Its meaning is:
   *   over the partial assignment a, var is not in interval because p~sc~0
   *   and the origin of this is constraint.
   *
   * @param var The variable for which the interval is excluded
   * @param vm A variable mapper between cvc5 and libpoly variables
   * @param p The polynomial of the constraint
   * @param a The current partial assignment
   * @param sc The sign condition of the constraint
   * @param interval The concrete interval that is excluded
   * @param constraint The assumption that yields p and sc
   */
  void addDirect(Node var,
                 VariableMapper& vm,
                 const poly::Polynomial& p,
                 const poly::Assignment& a,
                 const poly::Interval& interval,
                 Node constraint,
                 size_t intervalId);

  /**
   * Constructs the (generalized) interval that is to be excluded from a
   * CACInterval. It should be called after the recursive call to construct the
   * generalized sample necessary for endScope().
   *
   * @param var The variable for which the interval is excluded
   * @param i The concrete interval that is excluded
   * @param a The current partial assignment
   * @param s The sample point that is refuted for var
   * @param vm A variable mapper between cvc5 and libpoly variables
   */
  std::vector<Node> constructCell(Node var,
                                  const CACInterval& i,
                                  const poly::Assignment& a,
                                  const poly::Value& s,
                                  VariableMapper& vm);

 private:
  /** The list of generated proofs */
  CDProofSet<LazyTreeProofGenerator> d_proofs;
  /** The current proof */
  LazyTreeProofGenerator* d_current;

  /** Constant false */
  Node d_false;
  /** Constant zero */
  Node d_zero;

  CDProof* d_cdp;
  context::Context* d_ctx;
  std::vector<std::pair<poly::Polynomial, poly::Value>> d_polysRoots;
  std::vector<ProofInterval> d_intervals;
  RootMap d_rootMap;
  /** The variable the univariate proof is about */
  Node d_univVar;
};

/**
 * Prints the underlying LazyTreeProofGenerator. Please check the documentation
 * of std::ostream& operator<<(std::ostream&, const LazyTreeProofGenerator&)
 */
std::ostream& operator<<(std::ostream& os,
                         const CoveringsProofGenerator& proof);

}  // namespace coverings
}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
#endif
