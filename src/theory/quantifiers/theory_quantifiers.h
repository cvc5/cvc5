/*********************                                                        */
/*! \file theory_quantifiers.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Theory of quantifiers.
 **
 ** Theory of quantifiers.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H
#define CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H

#include "expr/node.h"
#include "theory/quantifiers/proof_checker.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_rewriter.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory.h"
#include "theory/valuation.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class TheoryQuantifiers : public Theory {
 public:
  TheoryQuantifiers(context::Context* c,
                    context::UserContext* u,
                    OutputChannel& out,
                    Valuation valuation,
                    const LogicInfo& logicInfo,
                    ProofNodeManager* pnm = nullptr);
  ~TheoryQuantifiers();

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** finish initialization */
  void finishInit() override;
  /** needs equality engine */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  //--------------------------------- end initialization

  void preRegisterTerm(TNode n) override;
  void presolve() override;
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;
  //--------------------------------- standard check
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  /** Pre-notify fact, return true if processed. */
  bool preNotifyFact(TNode atom,
                     bool pol,
                     TNode fact,
                     bool isPrereg,
                     bool isInternal) override;
  //--------------------------------- end standard check
  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  void shutdown() override {}
  std::string identify() const override
  {
    return std::string("TheoryQuantifiers");
  }
  void setUserAttribute(const std::string& attr,
                        Node n,
                        std::vector<Node> node_values,
                        std::string str_value) override;

 private:
  /** The theory rewriter for this theory. */
  QuantifiersRewriter d_rewriter;
  /** The proof rule checker */
  QuantifiersProofRuleChecker d_qChecker;
  /** The quantifiers state */
  QuantifiersState d_qstate;
  /** The quantifiers inference manager */
  QuantifiersInferenceManager d_qim;
  /** The quantifiers engine, which lives here */
  QuantifiersEngine d_qengine;
};/* class TheoryQuantifiers */

}/* CVC4::theory::quantifiers namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__QUANTIFIERS__THEORY_QUANTIFIERS_H */
