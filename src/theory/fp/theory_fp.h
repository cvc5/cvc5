/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Martin Brain
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

  Node getValue(TNode node);

  /** General utility. */
  void registerTerm(TNode node);
  bool isRegistered(TNode node);

  /** The word-blaster. Translates FP -> BV. */
  std::unique_ptr<FpWordBlaster> d_wordBlaster;

  void wordBlastAndEquateTerm(TNode node);

  /** Interaction with the rest of the solver **/
  void handleLemma(Node node, InferenceId id);
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

  bool refineAbstraction(TheoryModel* m, TNode abstract, TNode concrete);

  /** The terms registered via registerTerm(). */
  context::CDHashSet<Node> d_registeredTerms;

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
