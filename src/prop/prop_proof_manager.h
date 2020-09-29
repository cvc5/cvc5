/*********************                                                        */
/*! \file prop_proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof manager of PropEngine
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP_PROOF_MANAGER_H
#define CVC4__PROP_PROOF_MANAGER_H

#include "context/cdlist.h"
#include "expr/proof.h"
#include "expr/proof_node_manager.h"
#include "prop/proof_post_processor.h"
#include "prop/sat_proof_manager.h"

namespace CVC4 {

namespace prop {

/**
 * This class is responsible for managing the proof output of PropEngine, both
 * building and checking it.
 */
class PropPfManager
{
 public:
  PropPfManager(context::UserContext* userContext,
                ProofNodeManager* pnm,
                SatProofManager* satPM,
                ProofCnfStream* cnfProof);

  /** Saves assertion for later checking whether refutation proof is closed. */
  void registerAssertion(Node assertion);
  /**
   * Generates the prop engine proof: a proof of false resulting from the
   * connection of the refutation proof in d_satPM with the justification for
   * its assumptions, which are retrieved from the CNF conversion proof, if any.
   *
   * The connection is done by running the proof post processor d_pfpp over the
   * proof of false provided by d_satPM. See ProofPostProcessor for more
   * details.
   */
  std::shared_ptr<ProofNode> getProof();

  /**
   * Checks that the prop engine proof is closed w.r.t. the given assertions and
   * previously registered assertions in d_assertions. */
  void checkProof(context::CDList<Node>* assertions);

 private:
  /** A node manager */
  ProofNodeManager* d_pnm;
  /** The proof post-processor */
  std::unique_ptr<prop::ProofPostproccess> d_pfpp;
  /**
   * The SAT solver's proof manager, which will provide a refutation
   * proofresolution proof when requested */
  SatProofManager* d_satPM;
  /**
   * Assertions that should correspond to the leaves of the prop engine's proof.
   */
  context::CDList<Node> d_assertions;
}; /* class PropPfManager */

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__PROOF_MANAGER_H */
