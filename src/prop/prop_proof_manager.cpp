/*********************                                                        */
/*! \file prop_proof_manager
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
    : d_pnm(pnm),
      d_pfpp(new ProofPostproccess(pnm, cnfProof)),
      d_satPM(satPM),
      d_assertions(userContext)
{
  // add trivial assumption. This is so that we can check the that the prop
  // engine's proof is closed, as the SAT solver's refutation proof may use True
  // as an assumption even when True is not given as an assumption. An example
  // is when a propagated literal has an empty explanation (i.e., it is a valid
  // literal), which leads to adding True as its explanation, since for creating
  // a learned clause we need at least two literals.
  d_assertions.push_back(NodeManager::currentNM()->mkConst(true));
}

void PropPfManager::registerAssertion(Node assertion)
{
  d_assertions.push_back(assertion);
}

void PropPfManager::checkProof(context::CDList<Node>* assertions)
{
  Trace("sat-proof") << "PropPfManager::checkProof: Checking if resolution "
                        "proof of false is closed\n";
  std::shared_ptr<ProofNode> conflictProof = d_satPM->getProof();
  Assert(conflictProof);
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  // add given assertions d_assertions
  for (const Node& assertion : *assertions)
  {
    d_assertions.push_back(assertion);
  }
  std::vector<Node> avec{d_assertions.begin(), d_assertions.end()};
  pfnEnsureClosedWrt(
      conflictProof.get(), avec, "sat-proof", "PropPfManager::checkProof");
}

std::shared_ptr<ProofNode> PropPfManager::getProof()
{
  // retrieve the SAT solver's refutation proof
  Trace("sat-proof")
      << "PropPfManager::getProof: Getting resolution proof of false\n";
  std::shared_ptr<ProofNode> conflictProof = d_satPM->getProof();
  Assert(conflictProof);
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
    Trace("sat-proof-debug")
        << "PropPfManager::getProof: proof is " << *conflictProof.get() << "\n";
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
    Trace("sat-proof-debug")
        << "PropPfManager::getProof: proof is " << *conflictProof.get() << "\n";
  }
  return conflictProof;
}

}  // namespace prop
}  // namespace CVC4
