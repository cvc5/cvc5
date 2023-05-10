/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the proof manager for the PropPfManager.
 */

#include "prop/prop_proof_manager.h"

#include "proof/proof_ensure_closed.h"
#include "proof/proof_node_algorithm.h"
#include "prop/prop_proof_manager.h"
#include "prop/sat_solver.h"
#include "smt/env.h"

namespace cvc5::internal {
namespace prop {

PropPfManager::PropPfManager(Env& env,
                             context::UserContext* userContext,
                             CDCLTSatSolver* satSolver,
                             ProofCnfStream* cnfProof)
    : EnvObj(env),
      d_propProofs(userContext),
      d_pfpp(new ProofPostprocess(env, cnfProof)),
      d_satSolver(satSolver),
      d_assertions(userContext),
      d_proofCnfStream(cnfProof)
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

void PropPfManager::checkProof(const context::CDList<Node>& assertions)
{
  Trace("sat-proof") << "PropPfManager::checkProof: Checking if resolution "
                        "proof of false is closed\n";
  std::shared_ptr<ProofNode> conflictProof = d_satSolver->getProof();
  Assert(conflictProof);
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  // add given assertions d_assertions
  for (const Node& assertion : assertions)
  {
    d_assertions.push_back(assertion);
  }
  std::vector<Node> avec{d_assertions.begin(), d_assertions.end()};
  pfnEnsureClosedWrt(options(),
                     conflictProof.get(),
                     avec,
                     "sat-proof",
                     "PropPfManager::checkProof");
}

std::vector<std::shared_ptr<ProofNode>> PropPfManager::getProofLeaves(
    modes::ProofComponent pc)
{
  Trace("sat-proof") << "PropPfManager::getProofLeaves: Getting " << pc
                     << " component proofs\n";
  std::vector<Node> fassumps;
  Assert(pc == modes::PROOF_COMPONENT_THEORY_LEMMAS
         || pc == modes::PROOF_COMPONENT_PREPROCESS);
  std::vector<std::shared_ptr<ProofNode>> pfs =
      pc == modes::PROOF_COMPONENT_THEORY_LEMMAS
          ? d_proofCnfStream->getLemmaClausesProofs()
          : d_proofCnfStream->getInputClausesProofs();
  std::shared_ptr<ProofNode> satPf = getProof(false);
  std::vector<Node> satLeaves;
  expr::getFreeAssumptions(satPf.get(), satLeaves);
  std::vector<std::shared_ptr<ProofNode>> usedPfs;
  for (const std::shared_ptr<ProofNode>& pf : pfs)
  {
    Node proven = pf->getResult();
    if (std::find(satLeaves.begin(), satLeaves.end(), proven) != satLeaves.end())
    {
      usedPfs.push_back(pf);
    }
  }
  return usedPfs;
}

std::shared_ptr<ProofNode> PropPfManager::getProof(bool connectCnf)
{
  auto it = d_propProofs.find(connectCnf);
  if (it != d_propProofs.end())
  {
    return it->second;
  }
  // retrieve the SAT solver's refutation proof
  Trace("sat-proof")
      << "PropPfManager::getProof: Getting resolution proof of false\n";
  std::shared_ptr<ProofNode> conflictProof = d_satSolver->getProof();
  Assert(conflictProof);
  if (TraceIsOn("sat-proof"))
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
  if (!connectCnf)
  {
    d_propProofs[connectCnf] = conflictProof;
    return conflictProof;
  }
  // connect it with CNF proof
  d_pfpp->process(conflictProof);
  if (TraceIsOn("sat-proof"))
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
  d_propProofs[connectCnf] = conflictProof;
  return conflictProof;
}

}  // namespace prop
}  // namespace cvc5::internal
