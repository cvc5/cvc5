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
#include "prop/proof_post_processor.h"

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
                CDProof* satProof,
                ProofCnfStream* cnfProof);

  std::shared_ptr<ProofNode> getProof();

 private:
  /** A node manager */
  ProofNodeManager* d_pnm;
  /** The proof post-processor */
  std::unique_ptr<prop::ProofPostproccess> d_pfpp;
  /** The sat solver proof to be processed when the final proof is requested */
  CDProof* d_satProof;
}; /* class SmtEngine */

}  // namespace prop
}  // namespace CVC4

#endif /* CVC4__PROP__PROOF_MANAGER_H */
