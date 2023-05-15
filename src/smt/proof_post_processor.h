/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__SMT__PROOF_POST_PROCESSOR_H
#define CVC5__SMT__PROOF_POST_PROCESSOR_H

#include <map>
#include <sstream>
#include <unordered_set>

#include "proof/proof_node_updater.h"
#include "rewriter/rewrite_db_proof_cons.h"
#include "rewriter/rewrites.h"
#include "smt/env_obj.h"
#include "smt/proof_final_callback.h"
#include "smt/witness_form.h"
#include "theory/inference_id.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace smt {

/**
 * A callback class used by SolverEngine for post-processing proof nodes by
 * connecting proofs of preprocessing, and expanding macro PfRule applications.
 */
class ProofPostprocessCallback : public ProofNodeUpdaterCallback, protected EnvObj
{
 public:
  ProofPostprocessCallback(Env& env,
                           rewriter::RewriteDb* rdb,
                           bool updateScopedAssumptions);
  ~ProofPostprocessCallback() {}
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   *
   * @param pppg The proof generator that has proofs of preprocessed assertions
   * (derived from input assertions).
   */
  void initializeUpdate(ProofGenerator* pppg);
  /**
   * Set eliminate rule, which adds rule to the list of rules we will eliminate
   * during update. This adds rule to d_elimRules. Supported rules for
   * elimination include MACRO_*, SUBS and REWRITE. Otherwise, this method
   * has no effect.
   */
  void setEliminateRule(PfRule rule);
  /** set eliminate all trusted rules via DSL */
  void setEliminateAllTrustedRules();
  /** Should proof pn be updated? */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** Update the proof rule application. */
  bool update(Node res,
              PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

 private:
  /** Common constants */
  Node d_true;
  /** The proof checker we are using */
  ProofChecker* d_pc;
  /** The preprocessing proof generator */
  ProofGenerator* d_pppg;
  /** The rewrite database proof generator */
  rewriter::RewriteDbProofCons d_rdbPc;
  /** The witness form proof generator */
  WitnessFormGenerator d_wfpm;
  /** The witness form assumptions used in the proof */
  std::vector<Node> d_wfAssumptions;
  /** Kinds of proof rules we are eliminating */
  std::unordered_set<PfRule, PfRuleHashFunction> d_elimRules;
  /** Whether we are trying to eliminate any trusted rule via the DSL */
  bool d_elimAllTrusted;
  /** Whether we post-process assumptions in scope. */
  bool d_updateScopedAssumptions;
  //---------------------------------reset at the begining of each update
  /** Mapping assumptions to their proof from preprocessing */
  std::map<Node, std::shared_ptr<ProofNode> > d_assumpToProof;
  //---------------------------------end reset at the begining of each update
  /** Return true if id is a proof rule that we should expand */
  bool shouldExpand(PfRule id) const;
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
                    CDProof* cdp,
                    Node res = Node::null());
  /**
   * Update the proof rule application, called during expand macros when
   * we wish to apply the update method. This method has the same behavior
   * as update apart from ignoring the continueUpdate flag.
   */
  bool updateInternal(Node res,
                      PfRule id,
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
  /**
   * Add proof for substitution step. Some substitutions are derived based
   * on viewing a formula as a Boolean assignment (see MethodId::SB_LITERAL for
   * example). This method ensures that the proof of var == subs exists
   * in cdp, where var, subs were derived from BuiltinProofRuleChecker's
   * getSubstitution method.
   *
   * @param var The variable of the substitution
   * @param subs The substituted term
   * @param assump The formula the substitution was derived from
   * @param cdp The proof to add to
   * @return var == subs, the conclusion of the substitution step.
   */
  Node addProofForSubsStep(Node var, Node subs, Node assump, CDProof* cdp);
  /** Add eq (or its symmetry) to transivity children, if not reflexive */
  bool addToTransChildren(Node eq,
                          std::vector<Node>& tchildren,
                          bool isSymm = false);

};

/**
 * The proof postprocessor module. This postprocesses the final proof
 * produced by an SolverEngine. Its main two tasks are to:
 * (1) Connect proofs of preprocessing,
 * (2) Expand macro PfRule applications.
 */
class ProofPostprocess : protected EnvObj
{
 public:
  /**
   * @param env The environment we are using
   * @param updateScopedAssumptions Whether we post-process assumptions in
   * scope. Since doing so is sound and only problematic depending on who is
   * consuming the proof, it's true by default.
   */
  ProofPostprocess(Env& env,
                   rewriter::RewriteDb* rdb,
                   bool updateScopedAssumptions = true);
  ~ProofPostprocess();
  /** post-process
   *
   * @param pf The proof to process.
   * @param pppg The proof generator for pre-processing proofs.
   */
  void process(std::shared_ptr<ProofNode> pf, ProofGenerator* pppg);
  /** set eliminate rule */
  void setEliminateRule(PfRule rule);
  /** set eliminate all trusted rules via DSL */
  void setEliminateAllTrustedRules();

 private:
  /** The post process callback */
  ProofPostprocessCallback d_cb;
  /**
   * The updater, which is responsible for expanding macros in the final proof
   * and connecting preprocessed assumptions to input assumptions.
   */
  ProofNodeUpdater d_updater;
  /** The post process callback for finalization */
  ProofFinalCallback d_finalCb;
  /**
   * The finalizer, which is responsible for taking stats and checking for
   * (lazy) pedantic failures.
   */
  ProofNodeUpdater d_finalizer;
};

}  // namespace smt
}  // namespace cvc5::internal

#endif
