/*********************                                                        */
/*! \file proof_post_processor.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The module for processing proof nodes in the prop engine
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP__PROOF_POST_PROCESSOR_H
#define CVC4__PROP__PROOF_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "expr/proof_node_updater.h"

#include "prop/proof_cnf_stream.h"

namespace CVC4 {

namespace prop {

/**
 * A callback class used by PropEngine for post-processing proof nodes by
 * connecting proofs of resolution with CNF transformation and its generators.
 */
class ProofPostprocessCallback : public ProofNodeUpdaterCallback
{
 public:
  ProofPostprocessCallback(ProofNodeManager* pnm,
                           ProofCnfStream* proofCnfStream);
  ~ProofPostprocessCallback() {}
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update.
   */
  void initializeUpdate();
  /** Should proof pn be updated? */
  bool shouldUpdate(ProofNode* pn) override;
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
  /** The cnf stream proof generator */
  ProofCnfStream* d_proofCnfStream;
  //---------------------------------reset at the begining of each update
  /** Mapping assumptions to their proof from cnf transformation */
  std::map<Node, std::shared_ptr<ProofNode> > d_assumpToProof;
  //---------------------------------end reset at the begining of each update
};

/**
 * The proof postprocessor module. This postprocesses the final proof
 * produced by the Sat solver. Its main tasks is to connect its assumptions to
 * the CNF transformation proof in ProofCnfStream
 */
class ProofPostproccess
{
 public:
  ProofPostproccess(ProofNodeManager* pnm, ProofCnfStream* proofCnfStream);
  ~ProofPostproccess();
  /** post-process */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
  ProofPostprocessCallback d_cb;
  /** The proof node manager */
  ProofNodeManager* d_pnm;
};

}  // namespace prop
}  // namespace CVC4

#endif
