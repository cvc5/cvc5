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
#include "smt/witness_form.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/**
 * A callback class used by SmtEngine for post-processing proof nodes by
 * connecting proofs of preprocessing, and expanding macro PfRule applications.
 */
class ProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  ProofPostprocessCallback(ProofNodeManager* pnm,
                           SmtEngine* smte,
                           ProofGenerator* pppg);
  ~ProofPostprocessCallback() {}
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   */
  void initializeUpdate();
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
  /** Pointer to the SmtEngine, which should have proofs enabled */
  SmtEngine* d_smte;
  /** The preprocessing proof generator */
  ProofGenerator* d_pppg;
  /** The witness form proof generator */
  WitnessFormGenerator d_wfpm;
  /** The witness form assumptions used in the proof */
  std::vector<Node> d_wfAssumptions;
  /** Kinds of proof rules we are eliminating */
  std::unordered_set<PfRule, PfRuleHashFunction> d_elimRules;
  //---------------------------------reset at the begining of each update
  /** Mapping assumptions to their proof from preprocessing */
  std::map<Node, std::shared_ptr<ProofNode> > d_assumpToProof;
  //---------------------------------end reset at the begining of each update
  /**
   * Expand macros in the given application, add the expanded proof to cdp.
   */
  Node expandMacros(PfRule id,
                    const std::vector<Node>& children,
                    const std::vector<Node>& args,
                    CDProof* cdp);
  /** 
   * Add proof for witness form. This returns the equality t = toWitness(t)
   * and ensures that the proof of this equality has been added to cdp.
   * Notice the proof of this fact may have open assumptions of the form:
   *   k = toWitness(k)
   * where k is a skolem. Furthermore, note that all open assumptions of this
   * form are available via d_wfpm.getWitnessFormEqs() in the remainder of
   * the lifetime of this class.
   */
  Node addProofForWitnessForm(Node t,  CDProof* cdp);
  /** Apply transivity if necessary for the arguments */
  Node addProofForTrans(const std::vector<Node>& tchildren, CDProof* cdp);
  /** Add eq (or its symmetry) to transivity children, if not reflexive */
  bool addToTransChildren(Node eq, std::vector<Node>& tchildren, bool isSymm=false);
};

/** Statistics callback class */
class ProofPostprocessStatsCallback : public ProofNodeUpdaterCallback
{
 public:
  ProofPostprocessStatsCallback();
  ~ProofPostprocessStatsCallback();
  /** Should proof pn be updated? Returns false, adds to stats. */
  bool shouldUpdate(ProofNode* pn) override;

 private:
  /** Counts number of postprocessed proof nodes for each kind of proof rule */
  HistogramStat<PfRule> d_ruleCount;
  /** Total number of postprocessed rule applications */
  IntStat d_totalRuleCount;
};

/**
 * The proof postprocessor module. This postprocesses the final proof
 * produced by an SmtEngine. Its main two tasks are to:
 * (1) Connect proofs of preprocessing,
 * (2) Expand macro PfRule applications.
 */
class ProofPostproccess
{
 public:
  ProofPostproccess(ProofNodeManager* pnm,
                    SmtEngine* smte,
                    ProofGenerator* pppg);
  ~ProofPostproccess();
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);
  /** set eliminate rule */
  void setEliminateRule(PfRule rule);

 private:
  /** The post process callback */
  ProofPostprocessCallback d_cb;
  /** The post process callback for statistics */
  ProofPostprocessStatsCallback d_statCb;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace smt
}  // namespace CVC4

#endif
