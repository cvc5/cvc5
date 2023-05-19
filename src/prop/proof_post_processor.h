/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for processing proof nodes in the prop engine.
 */

#include "cvc5_private.h"

#ifndef CVC5__PROP__PROOF_POST_PROCESSOR_H
#define CVC5__PROP__PROOF_POST_PROCESSOR_H

#include <map>
#include <unordered_set>

#include "proof/proof_node_updater.h"
#include "prop/proof_cnf_stream.h"
#include "smt/env_obj.h"

namespace cvc5::internal {

namespace prop {

/**
 * A callback class used by PropEngine for post-processing proof nodes by
 * connecting proofs of resolution, whose leaves are clausified preprocessed
 * assertions and lemmas, with the CNF transformation of these formulas, while
 * expanding the generators of lemmas.
 */
class ProofPostprocessCallback : protected EnvObj,
                                 public ProofNodeUpdaterCallback
{
 public:
  ProofPostprocessCallback(Env& env, ProofCnfStream* proofCnfStream);
  ~ProofPostprocessCallback() {}
  /**
   * Initialize, called once for each new ProofNode to process. This initializes
   * static information to be used by successive calls to update. For this
   * callback it resets d_assumpToProof.
   */
  void initializeUpdate();
  /** Should proof pn be updated?
   *
   * For this callback a proof node is updatable if it's an assumption for which
   * the proof cnf straem has a proof. However if the proof node is blocked
   * (which is the case for proof nodes introduced into the proof cnf stream's
   * proof via expansion of its generators) then traversal is the proof node is
   * cancelled, i.e., continueUpdate is set to false.
   */
  bool shouldUpdate(std::shared_ptr<ProofNode> pn,
                    const std::vector<Node>& fa,
                    bool& continueUpdate) override;
  /** Update the proof rule application.
   *
   * Replaces assumptions by their proof in proof cnf stream. Note that in doing
   * this the proof node is blocked, so that future post-processing does not
   * traverse it.
   *
   * This method uses the cache in d_assumpToProof to avoid recomputing proofs
   * for the same assumption (in the same scope).
   */
  bool update(Node res,
              PfRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp,
              bool& continueUpdate) override;

 private:
  /** The cnf stream proof generator */
  ProofCnfStream* d_proofCnfStream;
  //---------------------------------reset at the begining of each update
  /** Mapping assumptions to their proof from cnf transformation */
  std::map<Node, std::shared_ptr<ProofNode> > d_assumpToProof;
  //---------------------------------end reset at the begining of each update
};

/**
 * The proof postprocessor module. This postprocesses the refutation proof
 * produced by the SAT solver. Its main task is to connect the refutation's
 * assumptions to the CNF transformation proof in ProofCnfStream.
 */
class ProofPostprocess : protected EnvObj
{
 public:
  ProofPostprocess(Env& env, ProofCnfStream* proofCnfStream);
  ~ProofPostprocess();
  /** post-process
   *
   * The post-processing is done via a proof node updater run on pf with this
   * class's callback d_cb.
   */
  void process(std::shared_ptr<ProofNode> pf);

 private:
  /** The post process callback */
  ProofPostprocessCallback d_cb;
};

}  // namespace prop
}  // namespace cvc5::internal

#endif
