/*********************                                                        */
/*! \file prop_proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof manager of PropEngine
 **/

#include "cvc4_private.h"

#ifndef CVC4__PROP_PROOF_MANAGER_H
#define CVC4__PROP_PROOF_MANAGER_H

#include "expr/proof.h"
#include "expr/proof_node_manager.h"
#include "options/smt_options.h"
#include "prop/proof_post_processor.h"
#include "prop/sat_proof_manager.h"

namespace CVC4 {

namespace prop {

/**
 * This class is responsible for managing the proof output of SmtEngine, as
 * well as setting up the global proof checker and proof node manager.
 */
class PropPfManager
{
 public:
  PropPfManager(ProofNodeManager* pnm,
                SatProofManager* satPM,
                ProofCnfStream* cnfProof);

  /** saves assertion for later checking whether final proved is closed */
  void registerAssertion(Node assertion);

  /**
   * Generates proof of false by connecting d_satProof the justification for its
   * assumptions being retrieved from the CNF conversion proof, if any.
   *
   * The connection is done by running the proof post processor d_pfpp over the
   * proof of false provided by d_satProof. For every assumption for which the
   * CNF proof has a non-assumption proof, this proof will replace the
   * assumption step.
   *
   * This method also optionally checks whether the remaining assumptions in the
   * proof of false are exactly the assertions registered to this proof manager,
   * which indicates whether a closed proof can be built.
   */
  std::shared_ptr<ProofNode> getProof();

 private:
  /** A node manager */
  ProofNodeManager* d_pnm;
  /** The proof post-processor */
  std::unique_ptr<prop::ProofPostproccess> d_pfpp;
  /** The sat solver proof manager, which will provide the final resolution proof when requested */
  SatProofManager* d_satPM;
  /** The assertions that should be the only assumptions of the postprocessed
   * proof */
  std::vector<Node> d_assertions;
}; /* class SmtEngine */

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__PROOF_MANAGER_H */
