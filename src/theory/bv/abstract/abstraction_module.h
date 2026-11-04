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
 * The lemma schemes are binary (they relate `x`, `s` and `t`), whereas cvc5's
 * BITVECTOR_MULT is n-ary and the rewriter flattens nested multiplications
 * into a single n-ary node. An n-ary multiplication is therefore left-
 * associated into a chain of binary multiplications, each of which is
 * abstracted by its own constant, e.g., `bvmul(a, b, c)` becomes `t2` with
 * `t1 = bvmul(a, b)` and `t2 = bvmul(t1, c)`. Every level of the chain must be
 * abstracted: the abstraction constant is what keeps the rewriter from
 * flattening the chain back into an n-ary node.
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
   * the abstraction map. Abstractable terms are bvmul/bvudiv/bvurem nodes whose
   * bit-width is at least the abstraction threshold (d_absSize); an n-ary
   * bvmul is left-associated into binary multiplications first, see binarize().
   *
   * @param fact The fact to abstract.
   * @return The abstracted fact (`fact` if nothing was abstracted).
   */
  Node abstract(TNode fact);

  /**
   * Check the current model for consistency with every abstracted term
   * and collect refinement lemmas.
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

  /**
   * Determine if a given node is a term that should be abstracted.
   * @param node The node to check.
   * @return True if `node` is a term that should be abstracted.
   * @note This includes n-ary multiplications, which are not abstracted by a
   *       single constant but binarized into a chain of abstracted binary
   *       multiplications (the n-ary node maps to the constant of the
   *       outermost chain element).
   */
  bool abstractable(TNode node) const;

  /** @return True if given node has been abstracted by a constant. */
  bool isAbstracted(TNode node) const;

  /**
   * Get the abstraction introduced for given node.
   * Asserts that the node has been abstracted.
   * @param node The node to get the abstraction for.
   * @return The abstraction.
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
   * Create abstraction constant for an abstractable *binary* `node`.
   *
   * Creates a fresh abstraction constant for each abstracted node and records
   * it in d_abs2node and d_cache.
   *
   * @param node The node to abstract.
   * @return The abstraction constant.
   */
  Node abstractNode(TNode node);

  /**
   * Left-associate an n-ary multiplication into binary multiplications and
   * abstract each of them, e.g., `bvmul(a, b, c)` yields `t2` with
   * `t1 = bvmul(a, b)` and `t2 = bvmul(t1, c)`.
   *
   * All chain elements have the same bit-width as `node` and thus are
   * abstractable iff `node` is. They are cached in d_cache, hence chains that
   * share a prefix (e.g., `bvmul(a, b, c)` and `bvmul(a, b, d)`) share the
   * abstraction constants of that prefix.
   *
   * @param node An abstractable BITVECTOR_MULT node with more than 2 children.
   * @return The abstraction constant of the outermost chain element.
   */
  Node binarize(TNode node);

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

  /**
   * Map from abstraction constant `t` to the node it abstracts. The abstracted
   * node is always binary (n-ary multiplications are binarized first), which
   * the binary lemma schemes of d_lemmas rely on.
   */
  std::unordered_map<Node, Node> d_abs2node;

  /**
   * Memoization cache for abstract(), maps abstracted node to their
   * abstraction constant `t`, and all other nodes to themselves. Also holds
   * the binary chain elements introduced for n-ary multiplications, which do
   * not occur in any fact themselves.
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
    /**
     * Number of arithmetic terms abstracted. Note that a binarized n-ary
     * multiplication of arity n accounts for n-1 of these, one per element of
     * its chain of binary multiplications.
     */
    IntStat d_numAbstractions;
    /** Number of n-ary multiplications binarized. */
    IntStat d_numBinarizations;
    /** Arities of the n-ary multiplications that were binarized. */
    HistogramStat<uint64_t> d_binarizedArity;
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
