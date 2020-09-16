/*********************                                                        */
/*! \file buffered_proof_generator.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of a proof generator for buffered proof steps
 **/

#include "expr/buffered_proof_generator.h"

#include "expr/proof.h"

namespace CVC4 {

BufferedProofGenerator::BufferedProofGenerator(context::Context* c,
                                               ProofNodeManager* pnm)
    : ProofGenerator(), d_facts(c), d_pnm(pnm)
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
  CDProof cdp(d_pnm);
  cdp.addStep(fact, *(*it).second);
  return cdp.getProofFor(fact);
}

}  // namespace CVC4
