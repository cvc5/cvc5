/*********************                                                        */
/*! \file veriT_post_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Hanna Lachnitt
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes into veriT proof nodes
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROOF__VERIT_PROOF_PROCESSOR_H
#define CVC4__PROOF__VERIT_PROOF_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "expr/proof_node_updater.h"

namespace CVC4 {

namespace proof {

/**
 * A callback class used by the veriT convereter for post-processing proof nodes
 * by replacing internal rules by the rules in the veriT calculus.
 */
class VeriTProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  VeriTProofPostprocessCallback(ProofNodeManager* pnm);
  ~VeriTProofPostprocessCallback() {}
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   */
  void initializeUpdate();
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
};

/**
 * The proof postprocessor module. This postprocesses a proof node into one
 * using the rules from the veriT calculus.
 */
class VeriTProofPostprocess : public ProofNodeUpdater 
{
 public:
  VeriTProofPostprocess(ProofNodeManager* pnm, ProofNodeUpdaterCallback &cb);
  ~VeriTProofPostprocess();
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
//	std::unique_ptr<VeriTProofPostprocessCallback> dd_cb;
  /** The proof node manager */
  //ProofNodeManager* dd_pnm;
};

}  // namespace proof
}  // namespace CVC4

#endif

