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

#include "theory/theory.h"
#include "expr/node.h"
#include "proof/arith_proof_recorder.h"
#include "theory/arith/theory_arith_private_forward.h"


namespace CVC4 {
namespace theory {

namespace arith {

/**
 * Implementation of QF_LRA.
 * Based upon:
 * http://research.microsoft.com/en-us/um/people/leonardo/cav06.pdf
 */
class TheoryArith : public Theory {
 private:
  friend class TheoryArithPrivate;

  TheoryArithPrivate* d_internal;

  TimerStat d_ppRewriteTimer;

  /**
   * @brief Where to store Farkas proofs of lemmas
   */
  proof::ArithProofRecorder * d_proofRecorder;

 public:
  TheoryArith(context::Context* c,
              context::UserContext* u,
              OutputChannel& out,
              Valuation valuation,
              const LogicInfo& logicInfo,
              ProofNodeManager* pnm = nullptr);
  virtual ~TheoryArith();

  TheoryRewriter* getTheoryRewriter() override;

  /**
   * Does non-context dependent setup for a node connected to a theory.
   */
  void preRegisterTerm(TNode n) override;

  void finishInit() override;

  TrustNode expandDefinition(Node node) override;

  void setMasterEqualityEngine(eq::EqualityEngine* eq) override;

  void check(Effort e) override;
  bool needsCheckLastEffort() override;
  void propagate(Effort e) override;
  TrustNode explain(TNode n) override;
  bool getCurrentSubstitution(int effort,
                              std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp) override;
  bool isExtfReduced(int effort,
                     Node n,
                     Node on,
                     std::vector<Node>& exp) override;

  bool collectModelInfo(TheoryModel* m) override;

  void shutdown() override {}

  void presolve() override;
  void notifyRestart() override;
  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions) override;
  TrustNode ppRewrite(TNode atom) override;
  void ppStaticLearn(TNode in, NodeBuilder<>& learned) override;

  std::string identify() const override { return std::string("TheoryArith"); }

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  void addSharedTerm(TNode n) override;

  Node getModelValue(TNode var) override;

  std::pair<bool, Node> entailmentCheck(
      TNode lit,
      const EntailmentCheckParameters* params,
      EntailmentCheckSideEffects* out) override;

  void setProofRecorder(proof::ArithProofRecorder* proofRecorder)
  {
    d_proofRecorder = proofRecorder;
  }

};/* class TheoryArith */

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
