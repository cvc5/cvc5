/*********************                                                        */
/*! \file lfsc_post_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes into Lfsc proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__LFSC__LFSC_POST_PROCESSOR_H
#define CVC4__PROOF__LFSC__LFSC_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "expr/proof_node_updater.h"
#include "proof/lfsc/lfsc_term_process.h"

namespace CVC4 {
namespace proof {

/**
 * A callback class used by the Lfsc convereter for post-processing proof nodes
 * by replacing internal rules by the rules in the Lfsc calculus.
 */
class LfscProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  LfscProofPostprocessCallback(ProofNodeManager* pnm);
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   */
  void initializeUpdate();
  /** Should update */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    bool& continueUpdate) override;
  /** Update the proof rule application. */
  bool update(Node res,
              PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

 private:
  /** The proof node manager */
  ProofNodeManager* d_pnm;
  /** The proof checker of d_pnm **/
  ProofChecker* d_pc;
  /** The term processor */
  LfscTermProcessor d_tproc;
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the Lfsc calculus.
 */
class LfscProofPostprocess
{
 public:
  LfscProofPostprocess(ProofNodeManager* pnm);
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
  std::unique_ptr<LfscProofPostprocessCallback> d_cb;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace proof
}  // namespace CVC4

#endif
