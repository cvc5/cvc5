/*********************                                                        */
/*! \file prop_proof_manager
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the proof manager for the PropPfManager
 **/

#include "prop/prop_proof_manager.h"

namespace CVC4 {
namespace prop {

PropPfManager::PropPfManager(ProofNodeManager* pnm,
                             CDProof* satProof,
                             ProofCnfStream* cnfProof)
    : d_pnm(pnm),
      d_pfpp(new ProofPostproccess(pnm, cnfProof)),
      d_satProof(satProof)
{
}

std::shared_ptr<ProofNode> PropPfManager::getProof()
{
  // retrieve the propositional conflict proof
  std::shared_ptr<ProofNode> conflictProof =
      d_satProof->getProofFor(NodeManager::currentNM()->mkConst(false))
          ->clone();
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  return conflictProof;
}

}  // namespace prop
}  // namespace CVC4
