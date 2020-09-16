/*********************                                                        */
/*! \file theory_arith.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Alex Ozdemir, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Arithmetic theory.
 ** Arithmetic theory.
 **/

#include "cvc4_private.h"

#pragma once

#include "expr/node.h"
#include "theory/arith/arith_state.h"
#include "theory/arith/inference_manager.h"
#include "theory/arith/theory_arith_private_forward.h"
#include "theory/theory.h"

namespace CVC4 {
namespace theory {
namespace arith {

namespace nl {
class NonlinearExtension;
}

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

  TrustNode expandDefinition(Node node) override;

  void check(Effort e) override;
  bool needsCheckLastEffort() override;
  void propagate(Effort e) override;
  TrustNode explain(TNode n) override;

  bool collectModelInfo(TheoryModel* m) override;
  /**
   * Collect model values in m based on the relevant terms given by termSet.
   */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  void shutdown() override {}

  void presolve() override;
  void notifyRestart() override;
  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions) override;
  TrustNode ppRewrite(TNode atom) override;
  void ppStaticLearn(TNode in, NodeBuilder<>& learned) override;

  std::string identify() const override { return std::string("TheoryArith"); }

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  void notifySharedTerm(TNode n) override;

  Node getModelValue(TNode var) override;

  std::pair<bool, Node> entailmentCheck(TNode lit) override;

  /** Return a reference to the arith::InferenceManager. */
  InferenceManager& getInferenceManager()
  {
    return d_inferenceManager;
  }

 private:
  /** The state object wrapping TheoryArithPrivate  */
  ArithState d_astate;

  /** The arith::InferenceManager. */
  InferenceManager d_inferenceManager;

  /**
   * The non-linear extension, responsible for all approaches for non-linear
   * arithmetic.
   */
  std::unique_ptr<nl::NonlinearExtension> d_nonlinearExtension;
};/* class TheoryArith */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
