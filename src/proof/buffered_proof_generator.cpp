/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of a proof generator for buffered proof steps.
 */

#include "proof/buffered_proof_generator.h"

#include "proof/proof.h"
#include "proof/proof_node_manager.h"

namespace cvc5::internal {

BufferedProofGenerator::BufferedProofGenerator(Env& env,
                                               context::Context* c,
                                               bool mkUniqueAssume,
                                               bool autoSymm)
    : EnvObj(env),
      ProofGenerator(),
      d_facts(c),
      d_mkUniqueAssume(mkUniqueAssume),
      d_autoSymm(autoSymm),
      d_assumptionsToPfNodes(c)
{
}

bool BufferedProofGenerator::addStep(Node fact,
                                     ProofStep ps,
                                     CDPOverwrite opolicy)
{
  // check duplicates if we are not always overwriting
  if (opolicy != CDPOverwrite::ALWAYS)
  {
    if (d_facts.find(fact) != d_facts.end())
    {
      // duplicate
      return false;
    }
    Node symFact = CDProof::getSymmFact(fact);
    if (!symFact.isNull())
    {
      if (d_facts.find(symFact) != d_facts.end())
      {
        // duplicate due to symmetry
        return false;
      }
    }
  }
  // note that this replaces the value fact is mapped to if there is already one
  d_facts.insert(fact, std::make_shared<ProofStep>(ps));
  return true;
}

std::shared_ptr<ProofNode> BufferedProofGenerator::getProofFor(Node fact)
{
  Trace("pfee-fact-gen") << "BufferedProofGenerator::getProofFor: " << fact
                         << std::endl;
  NodeProofStepMap::iterator it = d_facts.find(fact);
  if (it == d_facts.end())
  {
    if (!d_autoSymm)
    {
      return nullptr;
    }
    Node symFact = CDProof::getSymmFact(fact);
    if (symFact.isNull())
    {
      Trace("pfee-fact-gen") << "...cannot find step" << std::endl;
      Assert(false);
      return nullptr;
    }
    it = d_facts.find(symFact);
    if (it == d_facts.end())
    {
      Assert(false);
      Trace("pfee-fact-gen") << "...cannot find step (no sym)" << std::endl;
      return nullptr;
    }
  }
  Trace("pfee-fact-gen") << "...return via step " << *(*it).second << std::endl;
  CDProof cdp(d_env, nullptr, "CDProof", d_autoSymm);
  if (d_mkUniqueAssume)
  {
    // Add or create assumption proof nodes for children. If child has already
    // been seen, retrieve its saved assumption proof node, otherwise create via
    // cdp.
    for (const Node& n : it->second->d_children)
    {
      NodeProofNodeMap::iterator itChild = d_assumptionsToPfNodes.find(n);
      if (itChild != d_assumptionsToPfNodes.end())
      {
        cdp.addProof(itChild->second);
        continue;
      }
      // this call both creates an assumption proof node and saves it in cdp. We
      // use the resulting proof node to store in our cache.
      std::shared_ptr<ProofNode> pf = cdp.getProofFor(n);
      d_assumptionsToPfNodes.insert(n, pf);
    }
  }
  // If we are generating unique assumptions we require that we already have
  // proof steps for the premises. This must be guaranteed by the above loop and
  // is what prevents the duplication of assumption proof nodes (which will be
  // automatically created by the command below when they don't yet exist).
  cdp.addStep(fact, *(*it).second, d_mkUniqueAssume);
  return cdp.getProofFor(fact);
}

bool BufferedProofGenerator::hasProofFor(Node f)
{
  NodeProofStepMap::iterator it = d_facts.find(f);
  if (it == d_facts.end())
  {
    if (!d_autoSymm)
    {
      return false;
    }
    Node symFact = CDProof::getSymmFact(f);
    if (symFact.isNull())
    {
      return false;
    }
    it = d_facts.find(symFact);
    if (it == d_facts.end())
    {
      return false;
    }
  }
  return true;
}

}  // namespace cvc5::internal
