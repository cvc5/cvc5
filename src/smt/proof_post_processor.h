/*********************                                                        */
/*! \file proof_post_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__PROOF_POST_PROCESSOR_H
#define CVC4__SMT__PROOF_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "expr/proof_node_updater.h"

namespace CVC4 {
namespace smt {

/**
 * A callback class used by SmtEngine for post-processing proof nodes using
 * expand methods.
 */
class ProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  ProofPostprocessCallback(ProofNodeManager* pnm);
  ~ProofPostprocessCallback() {}
  /** set eliminate rule */
  void setEliminateRule(PfRule rule);
  /** Should proof pn be updated? */
  bool shouldUpdate(ProofNode* pn) override;
  /** Update the proof rule application. */
  bool update(PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp) override;

 private:
  /** Common constants */
  Node d_true;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The proof checker of the manager */
  ProofChecker* d_pchecker;
  /** Kinds of proof rules we are eliminating */
  std::unordered_set<PfRule, PfRuleHashFunction> d_elimRules;
  /** update internal */
  Node updateInternal(PfRule id,
                      const std::vector<Node>& children,
                      const std::vector<Node>& args,
                      CDProof* cdp);
};

/** The proof postprocessor module */
class ProofPostproccess
{
 public:
  ProofPostproccess(ProofNodeManager* pnm);
  ~ProofPostproccess();
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
  ProofPostprocessCallback d_cb;
  /** The proof node updater */
  ProofNodeUpdater d_updater;
};

}  // namespace smt
}  // namespace CVC4

#endif
