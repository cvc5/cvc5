/*********************                                                        */
/*! \file proof_node_updater.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A utility for updating proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__EXPR__PROOF_NODE_UPDATER_H
#define CVC4__EXPR__PROOF_NODE_UPDATER_H

#include <map>
#include <unordered_set>

#include "expr/proof_node.h"
#include "expr/proof_node_manager.h"
#include "expr/proof.h"

namespace CVC4 {

/**
 * A virtual callback class for updating ProofNode. An example use case of this
 * class is to eliminate a proof rule by expansion.
 */
class ProofNodeUpdaterCallback
{
 public:
  ProofNodeUpdaterCallback();
  virtual ~ProofNodeUpdaterCallback();
  /** Should proof pn be updated? */
  virtual bool shouldUpdate(ProofNode* pn) = 0;
  /**
   * Update the proof rule application, store steps in cdp. Return true if
   * the proof changed.
   */
  virtual bool update(PfRule id,
                      const std::vector<Node>& children,
                      const std::vector<Node>& args,
                      CDProof* cdp);
};

/**
 * A generic class for updating ProofNode. It is parameterized by a callback
 * class. It runs this callback on all subproofs of a provided ProofNode
 * application that meet some criteria (ProofNodeUpdaterCallback::shouldUpdate)
 * and overwrites them based on the update procedure of the callback
 * (ProofNodeUpdaterCallback::update).
 */
class ProofNodeUpdater
{
 public:
  ProofNodeUpdater(ProofNodeManager* pnm, ProofNodeUpdaterCallback& cb);
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The callback */
  ProofNodeUpdaterCallback& d_cb;
  /** Kinds of proof rules we are eliminating */
  // std::unordered_set<PfRule, PfRuleHashFunction> d_elimRules;
};

}  // namespace CVC4

#endif
