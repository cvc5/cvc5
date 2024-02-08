/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/env_obj.h"

namespace cvc5::internal {

class CDProof;
class ProofNode;
class ProofNodeManager;

/**
 * A virtual callback class for updating ProofNode. An example use case of this
 * class is to eliminate a proof rule by expansion.
 */
class ProofNodeConverterCallback
{
 public:
  ProofNodeConverterCallback();
  virtual ~ProofNodeConverterCallback();
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
  virtual Node convert(Node res,
                       ProofRule id,
                       const std::vector<Node>& children,
                       const std::vector<Node>& args,
                       CDProof* cdp) = 0;
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
class ProofNodeConverter : protected EnvObj
{
 public:
  /**
   * @param env Reference to the environment
   * @param cb The callback to apply to each node
   * @param autoSym Whether intermediate CDProof objects passed to updater
   * callbacks automatically introduce SYMM steps.
   */
  ProofNodeConverter(Env& env,
                      ProofNodeConverterCallback& cb,
                      bool autoSym = true);
  /**
   * Post-process, which performs the main post-processing technique described
   * above.
   */
  std::shared_ptr<ProofNode> process(std::shared_ptr<ProofNode> pf);
private:
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
   */
  std::shared_ptr<ProofNode> processInternal(std::shared_ptr<ProofNode> pf, const std::vector<std::shared_ptr<ProofNode>>& pchildren);
};

}  // namespace cvc5::internal

#endif
