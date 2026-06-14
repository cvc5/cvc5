/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Lazy proof generator for the lia* arithmetic extension.
 */

#ifdef CVC5_USE_NORMALIZ

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__LIASTAR__LIASTAR_PROOF_GENERATOR_H
#define CVC5__THEORY__ARITH__LIASTAR__LIASTAR_PROOF_GENERATOR_H

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/proof_generator.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

class ProofNode;

namespace theory {
namespace arith {
namespace liastar {

/**
 * Lazy proof generator for the lia* extension.
 *
 * The lia* extension emits three kinds of lemmas:
 *
 * (1) split:           `vp ∨ ¬vp` for the substituted vector predicate
 *                      `vp = p[v_1, ..., v_n]` of a literal
 *                      `(int.star-contains (lambda (x_1 ... x_n) p) v_1 ...
 * v_n)`. (2) non-negativity:  `(>= v_1 0) ∧ ... ∧ (>= v_n 0)` from a positive
 *                      polarity STAR_CONTAINS literal.
 * (3) reduction:       `(int.star-contains ... v) = star`, where `star` is
 *                      the cone/Hilbert-basis encoding produced by
 *                      `LiaStarExtension::getCones`.
 *
 * The generator records each lemma at lemma-send time and materializes a
 * concrete proof only when `getProofFor(fact)` is invoked at the end of
 * solving (i.e. the proofs are lazy). This makes the generator a natural
 * insertion point for subsolver-based proofs of (2) and (3): the hooks
 * `mkNonnegativeProof` and `mkContainsReduceProof` currently emit a single
 * `TRUST` step, but are intended to be replaced with a real proof obtained
 * from a subsolver call (cf. `proof_pipeline_notes.md`, §6 / §9 step 6).
 *
 * Lemma (1) is discharged with the existing `ProofRule::SPLIT` rule.
 */
class LiaStarProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  LiaStarProofGenerator(Env& env, context::Context* c);

  /**
   * Register a split lemma `vp ∨ ¬vp`.
   *
   * @param lemma the disjunction `vp ∨ ¬vp`
   * @param vectorPredicate the predicate `vp`
   */
  void registerSplit(Node lemma, Node vectorPredicate);

  /**
   * Register a non-negativity lemma derived from `literal`.
   *
   * @param lemma the non-negativity conjunction
   * @param literal the originating STAR_CONTAINS atom
   */
  void registerNonnegative(Node lemma, Node literal);

  /**
   * Register a STAR_CONTAINS reduction lemma `literal = star`.
   *
   * @param lemma the equality `(= literal star)`
   * @param literal the STAR_CONTAINS atom
   * @param star the cone-decomposition encoding
   */
  void registerContainsReduce(Node lemma, Node literal, Node star);

  /** ProofGenerator API. */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  bool hasProofFor(Node fact) override;
  std::string identify() const override;

 private:
  /** What kind of lemma a registered fact is. */
  enum class Kind : uint32_t
  {
    SPLIT,
    NONNEGATIVE,
    CONTAINS_REDUCE,
  };
  /**
   * Per-fact metadata. `d_kind` is the lemma kind; `d_aux` is:
   *  - SPLIT:           the vector predicate `vp`,
   *  - NONNEGATIVE:     the originating STAR_CONTAINS literal,
   *  - CONTAINS_REDUCE: the originating STAR_CONTAINS literal (the encoding
   *                     `star` is recoverable as `lemma[1]`).
   */
  struct Info
  {
    Kind d_kind;
    Node d_aux;
  };

  /**
   * Build the proof for the SPLIT lemma `vp ∨ ¬vp` using ProofRule::SPLIT.
   */
  std::shared_ptr<ProofNode> mkSplitProof(Node lemma, const Info& info);
  /**
   * Build the proof for a non-negativity lemma. Currently a TRUST step;
   * replace with a subsolver-discharged proof when ready.
   */
  std::shared_ptr<ProofNode> mkNonnegativeProof(Node lemma, const Info& info);
  /**
   * Build the proof for a STAR_CONTAINS reduction lemma. Currently a TRUST
   * step; replace with a subsolver-discharged proof when ready. The
   * subsolver should be asked to prove `lemma` (or refute its negation) and
   * its proof transcribed onto the parent ProofNodeManager (see
   * `proof_pipeline_notes.md`, §6, path (b)).
   */
  std::shared_ptr<ProofNode> mkContainsReduceProof(Node lemma,
                                                   const Info& info);

  /** Lemma -> kind map. */
  context::CDHashMap<Node, uint32_t> d_kind;
  /** Lemma -> auxiliary Node (see Info::d_aux). */
  context::CDHashMap<Node, Node> d_aux;
};

}  // namespace liastar
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__LIASTAR__LIASTAR_PROOF_GENERATOR_H */

#endif /* CVC5_USE_NORMALIZ */
