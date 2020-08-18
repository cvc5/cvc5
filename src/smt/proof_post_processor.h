/*********************                                                        */
/*! \file proof_post_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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
  /**
   * Set eliminate rule, which adds rule to the list of rules we will eliminate
   * during update. This adds rule to d_elimRules. Supported rules for
   * elimination include MACRO_*, SUBS and REWRITE. Otherwise, this method
   * has no effect.
   */
  void setEliminateRule(PfRule rule);
  /** Should proof pn be updated? */
  bool shouldUpdate(ProofNode* pn) override;
  /** Update the proof rule application. */
  bool update(Node res,
              PfRule id,
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
   * Expand rules in the given application, add the expanded proof to cdp.
   * The set of rules we expand is configured by calls to setEliminateRule
   * above. This method calls update to perform possible post-processing in the
   * rules it introduces as a result of the expansion.
   *
   * @param id The rule of the application
   * @param children The children of the application
   * @param args The arguments of the application
   * @param cdp The proof to add to
   * @return The conclusion of the rule, or null if this rule is not eliminated.
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
  Node addProofForWitnessForm(Node t, CDProof* cdp);
  /**
   * Apply transivity if necessary for the arguments. The nodes in
   * tchildren have been ordered such that they are legal arguments to TRANS.
   *
   * Returns the conclusion of the transitivity step, which is null if
   * tchildren is empty. Also note if tchildren contains a single element,
   * then no TRANS step is necessary to add to cdp.
   *
   * @param tchildren The children of a TRANS step
   * @param cdp The proof to add the TRANS step to
   * @return The conclusion of the TRANS step.
   */
  Node addProofForTrans(const std::vector<Node>& tchildren, CDProof* cdp);
  /** Add eq (or its symmetry) to transivity children, if not reflexive */
  bool addToTransChildren(Node eq,
                          std::vector<Node>& tchildren,
                          bool isSymm = false);
};

}  // namespace smt
}  // namespace CVC4

#endif
