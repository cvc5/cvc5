/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Arithmetic theory.
 */

#include "cvc5_private.h"

#pragma once

#include "expr/node.h"
#include "theory/arith/arith_preprocess.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/inference_manager.h"
#include "theory/theory.h"

namespace cvc5 {
namespace theory {
namespace arith {
namespace nl {
class NonlinearExtension;
}

class TheoryArithPrivate;

/**
 * Implementation of linear and non-linear integer and real arithmetic.
 * The linear arithmetic solver is based upon:
 * http://research.microsoft.com/en-us/um/people/leonardo/cav06.pdf
 */
class TheoryArith : public Theory {
 private:
  friend class TheoryArithPrivate;

  TheoryArithPrivate* d_internal;

  TimerStat d_ppRewriteTimer;

  /** Used to prove pp-rewrites */
  EagerProofGenerator d_ppPfGen;

 public:
  TheoryArith(context::Context* c,
              context::UserContext* u,
              OutputChannel& out,
              Valuation valuation,
              const LogicInfo& logicInfo,
              ProofNodeManager* pnm = nullptr);
  virtual ~TheoryArith();

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;
  /**
   * Returns true if this theory needs an equality engine, which is assigned
   * to it (d_equalityEngine) by the equality engine manager during
   * TheoryEngine::finishInit, prior to calling finishInit for this theory.
   * If this method returns true, it stores instructions for the notifications
   * this Theory wishes to receive from its equality engine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization
  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n) override;

  //--------------------------------- standard check
  /** Pre-check, called before the fact queue of the theory is processed. */
  bool preCheck(Effort level) override;
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  /** Pre-notify fact, return true if processed. */
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  //--------------------------------- end standard check
  bool needsCheckLastEffort() override;
  void propagate(Effort e) override;
  TrustNode explain(TNode n) override;

  bool collectModelInfo(TheoryModel* m, const std::set<Node>& termSet) override;
  /**
   * Collect model values in m based on the relevant terms given by termSet.
   */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  void shutdown() override {}

  void presolve() override;
  void notifyRestart() override;
  PPAssertStatus ppAssert(TrustNode tin,
                          TrustSubstitutionMap& outSubstitutions) override;
  /**
   * Preprocess rewrite terms, return the trust node encapsulating the
   * preprocessed form of n, and the proof generator that can provide the
   * proof for the equivalence of n and this term.
   *
   * This calls the operator elimination utility to eliminate extended
   * symbols.
   */
  TrustNode ppRewrite(TNode atom, std::vector<SkolemLemma>& lems) override;
  void ppStaticLearn(TNode in, NodeBuilder& learned) override;

  std::string identify() const override { return std::string("TheoryArith"); }

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  void notifySharedTerm(TNode n) override;

  Node getModelValue(TNode var) override;

  std::pair<bool, Node> entailmentCheck(TNode lit) override;

  /** Return a reference to the arith::InferenceManager. */
  InferenceManager& getInferenceManager()
  {
    return d_im;
  }

 private:
  /**
   * Preprocess equality, applies ppRewrite for equalities. This method is
   * distinct from ppRewrite since it is not allowed to construct lemmas.
   */
  TrustNode ppRewriteEq(TNode eq);
  /** Get the proof equality engine */
  eq::ProofEqEngine* getProofEqEngine();
  /** The state object wrapping TheoryArithPrivate  */
  ArithState d_astate;
  /** The arith::InferenceManager. */
  InferenceManager d_im;

  /**
   * The non-linear extension, responsible for all approaches for non-linear
   * arithmetic.
   */
  std::unique_ptr<nl::NonlinearExtension> d_nonlinearExtension;
  /** The operator elimination utility */
  OperatorElim d_opElim;
  /** The preprocess utility */
  ArithPreprocess d_arithPreproc;
  /** The theory rewriter for this theory. */
  ArithRewriter d_rewriter;

};/* class TheoryArith */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5
