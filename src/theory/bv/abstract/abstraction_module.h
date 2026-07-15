/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The bit-vector arithmetic abstraction module.
 *
 * Implements the abstraction module of the CEGAR strategy of "Scalable
 * Bit-Blasting with Abstractions" (Niemetz, Preiner, Zohar, CAV 2024).
 *
 * Arithmetic terms that are considered expensive for bit-blasting are replaced
 * with a fresh bit-vector constant `t` of the same sort. We introduce these
 * abstractions for arithmetic terms `op(x, s)` with op in {bvmul, bvudiv,
 * bvurem} whose bit-width is at least a configurable threshold.
 *
 * This over-approximates the bit-vector facts that come in. If an abstraction
 * is consistent wrt. the semantics of the abstracted arithmetic operation, it
 * is refined via a tiered refined strategy. The first tier is implemented by
 * the lemma schemes in abstraction_lemmas.h.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__ABSTRACT__BV_ABSTRACTION_H
#define CVC5__THEORY__BV__ABSTRACT__BV_ABSTRACTION_H

#include <unordered_map>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/bv/abstract/abstraction_lemmas.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

class TheoryBV;

namespace abstract {

/**
 * The bit-vector arithmetic abstraction module.
 */
class AbstractionModule : protected EnvObj
{
 public:
  /**
   * Constructor.
   * @param env The associated environment.
   * @param bv  The associated TheoryBV.
   */
  AbstractionModule(Env& env, TheoryBV* bv);

  /**
   * Replace every abstractable arithmetic subterm of `fact` (down to theory
   * leaves, we do not descend into theory leafs) by a fresh constant, recording
   * the abstraction map. Abstractable terms are binary bvmul/bvudiv/bvurem
   * nodes whose bit-width is at least the abstraction threshold (d_absSize).
   *
   * @param fact The fact to abstract.
   * @return The abstracted fact (`fact` if nothing was abstracted).
   */
  Node abstract(TNode fact);

  /**
   * Check the current model for consistency with every abstracted terms
   * and collect refinemente lemmas.
   *
   * For each abstracted term, to check consistency with the actual semantics
   * of the abstracted operation, its value under the current model is evaluated
   * via `TheoryBV::getValue()`. In case of inconsistency, one violated lemma
   * per abstracted term is collected. This is "lazy" on purpose as to not
   * overwhelm the SAT solver with refinement lemmas. If no tier-1/2 lemmas are
   * violated and the allowance for adding value instantiation lemmas (tier-3)
   * has been exhausted, a bit-blasting lemma (tier-4) is added.
   *
   * @param lemmas Output parameter, the collected refinement lemmas.
   */
  void check(std::vector<Node>& lemmas);

  /** @return True if `n` is a term that should be abstracted. */
  bool abstractable(TNode n) const;

  /** @return True if given node has been abstracted by a constant. */
  bool isAbstracted(TNode node) const;

  /**
   * @return The abstraction introduced for given node. Asserts that the
   *         node has been abstracted.
   */
  TNode getAbstraction(TNode node) const;

#ifdef CVC5_ASSERTIONS
  /**
   * @return True if every abstracted term is consistent with the current model,
   *         i.e. `op(v_x, v_s) == v_t` for each `t = op(x, s)`. Used as a debug
   *         check after the refinement loop concludes sat.
   */
  bool isModelConsistent();
#endif

 private:
  /**
   * @return The abstraction constant for an abstractable `node`. Creates a
   *         fresh abstraction constant for each abstracted node.
   */
  Node abstractNode(TNode node);

  /** The associated bit-vector theory engine. */
  TheoryBV* d_bv;

  /** Minimum bit-width to abstract (option --bv-abstraction-size). */
  uint64_t d_absSize;
  /**
   * Limiter for value instantiations, limit is <num insts> < bvsize/d_valLim
   * for each abstracted node (option --bv-abstraction-value-limiter).
   */
  uint64_t d_valLimiter;

  /** The refinement lemma schemes, used by the refinement loop. */
  LemmaRegistry d_lemmas;

  /** Map from abstraction constant `t` to the node it abstracts. */
  std::unordered_map<Node, Node> d_abs2node;

  /**
   * Memoization cache for abstract(), maps abstracted node to their
   * abstraction constant `t`, and all other nodes to themselves.
   */
  std::unordered_map<Node, Node> d_cache;

  /**
   * Number of tier-3 value-instantiation lemmas added so far for each
   * abstraction constant. Once this reaches the per-term budget
   * (bit-width / bvAbstractionValueInstDivisor), the tier-4 bit-blasting
   * fallback is used instead.
   */
  std::unordered_map<Node, uint64_t> d_valueInstCount;

  /** Statistics for the abstraction module. */
  struct Statistics
  {
    Statistics(StatisticsRegistry& reg);
    /** Number of arithmetic terms abstracted. */
    IntStat d_numAbstractions;
    /** Number of refinement consistency checks (refinement rounds). */
    IntStat d_numChecks;
    /** Number of tier-1/2 (Table-2 scheme) refinement lemmas added. */
    IntStat d_numLemmasTier12;
    /** Number of tier-3 value-instantiation refinement lemmas added. */
    IntStat d_numLemmasTier3;
    /** Number of tier-4 bit-blasting fallback lemmas added. */
    IntStat d_numLemmasTier4;
  } d_stats;
};

}  // namespace abstract
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif
