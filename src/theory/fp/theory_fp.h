/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Theory of floating-point arithmetic.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__FP__THEORY_FP_H
#define CVC5__THEORY__FP__THEORY_FP_H

#include <string>
#include <utility>

#include "context/cdhashset.h"
#include "context/cdo.h"
#include "theory/fp/theory_fp_rewriter.h"
#include "theory/theory.h"
#include "theory/theory_eq_notify.h"
#include "theory/theory_inference_manager.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace fp {

class FpWordBlaster;

class TheoryFp : public Theory
{
 public:
  /** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
  TheoryFp(Env& env, OutputChannel& out, Valuation valuation);

  //--------------------------------- initialization
  /** Get the official theory rewriter of this theory. */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;
  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  /** Finish initialization. */
  void finishInit() override;
  //--------------------------------- end initialization

  void preRegisterTerm(TNode node) override;
  TrustNode ppRewrite(TNode node, std::vector<SkolemLemma>& lems) override;

  //--------------------------------- standard check
  /** Do we need a check call at last call effort? */
  bool needsCheckLastEffort() override;
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  /** Pre-notify fact, return true if processed. */
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  //--------------------------------- end standard check

  bool collectModelInfo(TheoryModel* m,
                        const std::set<Node>& relevantTerms) override;
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  std::string identify() const override { return "THEORY_FP"; }

  TrustNode explain(TNode n) override;

  Node getCandidateModelValue(TNode node) override;

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

 private:
  using ConversionAbstractionMap = context::CDHashMap<TypeNode, Node>;
  using AbstractionMap = context::CDHashMap<Node, Node>;

  void notifySharedTerm(TNode n) override;

  /** General utility. */
  void registerTerm(TNode node);
  bool isRegistered(TNode node);

  /** The word-blaster. Translates FP -> BV. */
  std::unique_ptr<FpWordBlaster> d_wordBlaster;

  void wordBlastAndEquateTerm(TNode node);

  /**
   * Interaction with the rest of the solver.
   * Returns true if a new (non-trivial, not previously cached) lemma was sent.
   */
  bool handleLemma(Node node, InferenceId id);
  /**
   * Called when literal node is inferred by the equality engine. This
   * propagates node on the output channel.
   */
  bool propagateLit(TNode node);
  /**
   * Called when two constants t1 and t2 merge in the equality engine. This
   * sends a conflict on the output channel.
   */
  void conflictEqConstantMerge(TNode t1, TNode t2);

  /**
   * Refine the abstraction of a Real<->FP conversion against the current
   * candidate model.
   *
   * Conversions between reals and floating-point numbers cannot be
   * word-blasted and are instead abstracted at registration: registerTerm()
   * replaces the conversion by a fresh skolem `abstract`, maps it in
   * d_abstractionMap to a copy `concrete` of the conversion over purified
   * (leaf) arguments (see purifyArgument), and sends lemmas fixing the value
   * of the abstraction for the special cases (for fp.to_real: NaN/infinity
   * arguments yield the undefined-value argument, zero yields 0; for to_fp
   * from Real: the result is never NaN, a zero argument yields +zero).
   *
   * Called from postCheck() at LAST_CALL effort for every abstraction that
   * occurs in the candidate model. Compares the model value of `abstract`
   * against the exact conversion result computed from the model values of
   * the arguments of `concrete`:
   *
   * - If the values agree, the abstraction is exact for this model and no
   *   lemma is sent.
   * - If they disagree on argument values for which refinement is sound
   *   (normal/subnormal float for fp.to_real, non-NaN values for to_fp),
   *   refinement lemmas anchored at the current model values are sent: for
   *   fp.to_real, order equivalences around the argument and result values;
   *   for to_fp, monotonicity implications plus exact rounding-cell boundary
   *   equivalences (see utils::roundingCellLowerBound) that exclude the
   *   entire spurious rounding cell under the model's rounding mode.
   * - If no progress is possible -- the model values are non-constant (model
   *   construction in another theory failed), they contradict the
   *   registration lemmas (NaN/infinity/zero cases), or every refinement
   *   lemma was already sent in a previous round -- the model cannot be
   *   trusted and is marked unsound via
   *   IncompleteId::FP_ABSTRACTION_REFINEMENT, making the solver answer
   *   unknown rather than sat on it.
   *
   * @param m The current candidate model.
   * @param abstract The abstraction skolem standing for the conversion.
   * @param concrete The abstracted conversion, a FLOATINGPOINT_TO_REAL_TOTAL
   *                 or FLOATINGPOINT_TO_FP_FROM_REAL node over purified
   *                 arguments, as stored in d_abstractionMap.
   * @return True if a new refinement lemma was sent (the candidate model was
   *         refuted and another check round is required); false if the
   *         abstraction agreed with the model or nothing new could be
   *         learned (in the latter case the model has been marked unsound).
   */
  bool refineAbstraction(TheoryModel* m, TNode abstract, TNode concrete);

  /**
   * Purifies an argument of an abstracted conversion: non-leaf terms are
   * replaced by a purification skolem (with the defining equality sent as a
   * lemma) so that model values for the argument are leaf assignments and
   * cannot be corrupted by bottom-up evaluation of unrefined subterms.
   */
  Node purifyArgument(TNode n);

  /** The terms registered via registerTerm(). */
  context::CDHashSet<Node> d_registeredTerms;

  /** The arguments purified via purifyArgument(). */
  context::CDHashSet<Node> d_purifiedArgs;

  /** Map abstraction skolem to abstracted FP_TO_REAL/FP_FROM_REAL node. */
  AbstractionMap d_abstractionMap;  // abstract -> original

  /** The theory rewriter for this theory. */
  TheoryFpRewriter d_rewriter;
  /** A (default) theory state object. */
  TheoryState d_state;
  /** A (default) inference manager. */
  TheoryInferenceManager d_im;
  /** The notify class for equality engine. */
  TheoryEqNotifyClass d_notify;

  /** Cache of word-blasted facts. */
  context::CDHashSet<Node> d_wbFactsCache;

  /** Flag indicating whether `d_modelCache` should be invalidated. */
  context::CDO<bool> d_invalidateModelCache;

  /**
   * Cache for getValue() calls.
   *
   * Is cleared at the beginning of a getValue() call if the
   * `d_invalidateModelCache` flag is set to true.
   */
  std::unordered_map<Node, Node> d_modelCache;

  /** True constant. */
  Node d_true;
};

}  // namespace fp
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__FP__THEORY_FP_H */
