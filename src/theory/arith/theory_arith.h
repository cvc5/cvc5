/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/arith/arith_subs.h"
#include "theory/arith/branch_and_bound.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/pp_rewrite_eq.h"
#include "theory/arith/proof_checker.h"
#include "theory/theory.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {
class NonlinearExtension;
}

class EqualitySolver;

namespace linear {
class TheoryArithPrivate;
}

/**
 * Implementation of linear and non-linear integer and real arithmetic.
 * The linear arithmetic solver is based upon:
 * http://research.microsoft.com/en-us/um/people/leonardo/cav06.pdf
 */
class TheoryArith : public Theory {
  friend class linear::TheoryArithPrivate;
 public:
  TheoryArith(Env& env, OutputChannel& out, Valuation valuation);
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
  TrustNode ppStaticRewrite(TNode atom) override;
  void ppStaticLearn(TNode in, NodeBuilder& learned) override;

  std::string identify() const override { return std::string("TheoryArith"); }

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  void notifySharedTerm(TNode n) override;

  Node getCandidateModelValue(TNode var) override;

  std::pair<bool, Node> entailmentCheck(TNode lit) override;

  /** Return a reference to the arith::InferenceManager. */
  InferenceManager& getInferenceManager()
  {
    return d_im;
  }

 private:
  /**
   * Update d_arithModelCache (if it is empty right now) and compute the termSet
   * by calling collectAssertedTerms.
   */
  void updateModelCache(std::set<Node>& termSet);
  /**
   * Update d_arithModelCache (if it is empty right now) using the given
   * termSet.
   */
  void updateModelCacheInternal(const std::set<Node>& termSet);
  /**
   * Finalized model cache. Called after d_arithModelCache is finalized during
   * a full effort check. It computes d_arithModelCacheSubs/Vars, which are
   * used during theory combination, for getEqualityStatus.
   */
  void finalizeModelCache();
  /**
   * Perform a sanity check on the model that all integer variables are assigned
   * to integer values. If an integer variables is assigned to a non-integer
   * value, but the respective lemma can not be added (i.e. it has already been
   * added) an assertion triggers. Otherwise teturns true if a lemma was added,
   * false otherwise.
   */
  bool sanityCheckIntegerModel();

  /** Get the proof equality engine */
  eq::ProofEqEngine* getProofEqEngine();
  /** Timer for ppRewrite */
  TimerStat d_ppRewriteTimer;
  /** The state object  */
  TheoryState d_astate;
  /** The arith::InferenceManager. */
  InferenceManager d_im;
  /** The preprocess rewriter for equality */
  PreprocessRewriteEq d_ppre;
  /** The branch and bound utility */
  BranchAndBound d_bab;
  /** The equality solver */
  std::unique_ptr<EqualitySolver> d_eqSolver;
  /** The (old) linear arithmetic solver */
  linear::TheoryArithPrivate* d_internal;

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

  /**
   * Caches the current arithmetic model with the following life cycle:
   * postCheck retrieves the model from arith_private and puts it into the
   * cache. If nonlinear reasoning is enabled, the cache is used for (and
   * possibly updated by) model-based refinement in postCheck.
   * In collectModelValues, the cache is filtered for the termSet and then
   * used to augment the TheoryModel.
   */
  std::map<Node, Node> d_arithModelCache;
  /** Component of the above that was ill-typed */
  std::map<Node, Node> d_arithModelCacheIllTyped;
  /** The above model cache, in substitution form. */
  ArithSubs d_arithModelCacheSubs;
  /** Is the above map computed? */
  bool d_arithModelCacheSet;
  /** Checks the proof rules of this theory. */
  ArithProofRuleChecker d_checker;

};/* class TheoryArith */

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
