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

#include "expr/proof_node_algorithm.h"

namespace CVC4 {
namespace prop {

PropPfManager::PropPfManager(context::UserContext* userContext,
                             ProofNodeManager* pnm,
                             SatProofManager* satPM,
                             ProofCnfStream* cnfProof)
    : d_pnm(pnm), d_pfpp(new ProofPostproccess(pnm, cnfProof)), d_satPM(satPM), d_assertions(userContext)
{
}

void PropPfManager::registerAssertion(Node assertion)
{
  d_assertions.push_back(assertion);
}

std::shared_ptr<ProofNode> PropPfManager::getProof()
{
  // retrieve the propositional conflict proof
  Trace("sat-proof")
      << "PropPfManager::getProof: Getting resolution proof of false\n";
  std::shared_ptr<ProofNode> conflictProof = d_satPM->getProof()->getProofFor(
      NodeManager::currentNM()->mkConst(false));
  if (Trace.isOn("sat-proof"))
  {
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(conflictProof.get(), fassumps);
    Trace("sat-proof")
        << "PropPfManager::getProof: initial free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof") << "PropPfManager::getProof: proof is "
                       << *conflictProof.get() << "\n";
    Trace("sat-proof")
        << "PropPfManager::getProof: Connecting with CNF proof\n";
  }
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  if (Trace.isOn("sat-proof"))
  {
    std::vector<Node> fassumps;
    expr::getFreeAssumptions(conflictProof.get(), fassumps);
    Trace("sat-proof")
        << "PropPfManager::getProof: new free assumptions are:\n";
    for (const Node& a : fassumps)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof") << "PropPfManager::getProof: assertions are:\n";
    for (const Node& a : d_assertions)
    {
      Trace("sat-proof") << "- " << a << "\n";
    }
    Trace("sat-proof") << "PropPfManager::getProof: proof is "
                       << *conflictProof.get() << "\n";
  }
  if (options::proofNewEagerChecking())
  {
    Trace("sat-proof")
        << "PropPfManager::getProof: checking if can make scope...\n";
    // convert to vector
    std::vector<Node> avec;
    for (const Node& as : d_assertions)
    {
      avec.push_back(as);
    }
    std::shared_ptr<ProofNode> scopePfn =
        d_pnm->mkScope(conflictProof, avec);
    Trace("sat-proof") << "PropPfManager::getProof: prop engine prood is "
                          "closed w.r.t. preprocessed assertions\n";
  }
  return conflictProof;
}

}  // namespace prop
}  // namespace CVC4
