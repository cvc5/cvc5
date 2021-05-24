/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for updating proof nodes.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_NODE_UPDATER_H
#define CVC5__PROOF__PROOF_NODE_UPDATER_H

#include <map>
#include <memory>

#include "expr/node.h"
#include "proof/proof_node.h"

namespace cvc5 {

class CDProof;
class ProofNode;
class ProofNodeManager;

/**
 * A virtual callback class for updating ProofNode. An example use case of this
 * class is to eliminate a proof rule by expansion.
 */
class ProofNodeUpdaterCallback
{
 public:
  ProofNodeUpdaterCallback();
  virtual ~ProofNodeUpdaterCallback();
  /** Should proof pn be updated?
   *
   * @param pn the proof node that maybe should be updated
   * @param fa the assumptions in scope
   * @param continueUpdate whether we should continue recursively updating pn
   * @return whether we should run the update method on pn
   */
  virtual bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                            const std::vector<Node>& fa,
                            bool& continueUpdate) = 0;
  /**
   * Update the proof rule application, store steps in cdp. Return true if
   * the proof changed. It can be assumed that cdp contains proofs of each
   * fact in children.
   *
   * If continueUpdate is set to false in this method, then the resulting
   * proof (the proof of res in cdp) is *not* called back to update by the
   * proof node updater, nor are its children recursed. Otherwise, by default,
   * the proof node updater will continue updating the resulting proof and will
   * recursively update its children. This is analogous to marking REWRITE_DONE
   * in a rewrite response.
   */
  virtual bool update(Node res,
                      PfRule id,
                      const std::vector<Node>& children,
                      const std::vector<Node>& args,
                      CDProof* cdp,
                      bool& continueUpdate);
};

/**
 * A generic class for updating ProofNode. It is parameterized by a callback
 * class. Its process method runs this callback on all subproofs of a provided
 * ProofNode application that meet some criteria
 * (ProofNodeUpdaterCallback::shouldUpdate)
 * and overwrites them based on the update procedure of the callback
 * (ProofNodeUpdaterCallback::update), which uses local CDProof objects that
 * should be filled in the callback for each ProofNode to update. This update
 * process is applied in a *pre-order* traversal.
 */
class ProofNodeUpdater
{
 public:
  /**
   * @param pnm The proof node manager we are using
   * @param cb The callback to apply to each node
   * @param mergeSubproofs Whether to automatically merge subproofs within
   * the same SCOPE that prove the same fact.
   * @param autoSym Whether intermediate CDProof objects passed to updater
   * callbacks automatically introduce SYMM steps.
   */
  ProofNodeUpdater(ProofNodeManager* pnm,
                   ProofNodeUpdaterCallback& cb,
                   bool mergeSubproofs = false,
                   bool autoSym = true);
  /**
   * Post-process, which performs the main post-processing technique described
   * above.
   */
  void process(std::shared_ptr<ProofNode> pf);

  /**
   * Set free assumptions to freeAssumps. This indicates that we expect
   * the proof we are processing to have free assumptions that are in
   * freeAssumps. This enables checking when this is violated, which is
   * expensive in general. It is not recommended that this method is called
   * by default.
   */
  void setDebugFreeAssumptions(const std::vector<Node>& freeAssumps);

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The callback */
  ProofNodeUpdaterCallback& d_cb;
  /**
   * Post-process, which performs the main post-processing technique described
   * above.
   *
   * @param pf The proof to process
   * @param fa The assumptions of the scope that fa is a subproof of with
   * respect to the original proof. For example, if (SCOPE P :args (A B)), we
   * may call this method on P with fa = { A, B }.
   * @param traversing The list of proof nodes we are currently traversing
   * beneath. This is used for checking for cycles in the overall proof.
   */
  void processInternal(std::shared_ptr<ProofNode> pf,
                       const std::vector<Node>& fa,
                       std::vector<std::shared_ptr<ProofNode>>& traversing);
  /**
   * Update proof node cur based on the callback. This modifies curr using
   * ProofNodeManager::updateNode based on the proof node constructed to
   * replace it by the callback. Return true if cur was updated. If
   * continueUpdate is updated to false, then cur is not updated further
   * and its children are not traversed.
   */
  bool runUpdate(std::shared_ptr<ProofNode> cur,
                 const std::vector<Node>& fa,
                 bool& continueUpdate);
  /**
   * Finalize the node cur. This is called at the moment that it is established
   * that cur will appear in the final proof. We do any final debug checking
   * and add it to the results cache resCache if we are merging subproofs.
   */
  void runFinalize(std::shared_ptr<ProofNode> cur,
                   const std::vector<Node>& fa,
                   std::map<Node, std::shared_ptr<ProofNode>>& resCache);
  /** Are we debugging free assumptions? */
  bool d_debugFreeAssumps;
  /** The initial free assumptions */
  std::vector<Node> d_freeAssumps;
  /** Whether we are merging subproofs */
  bool d_mergeSubproofs;
  /**
   * Whether intermediate CDProof objects passed to updater callbacks
   * automatically introduce SYMM steps.
   */
  bool d_autoSym;
};

}  // namespace cvc5

#endif
