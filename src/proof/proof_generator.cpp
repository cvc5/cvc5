/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of proof generator utility.
 */

#include "proof/proof_generator.h"

#include <sstream>

#include "options/smt_options.h"
#include "proof/proof.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, CDPOverwrite opol)
{
  switch (opol)
  {
    case CDPOverwrite::ALWAYS: out << "ALWAYS"; break;
    case CDPOverwrite::ASSUME_ONLY: out << "ASSUME_ONLY"; break;
    case CDPOverwrite::NEVER: out << "NEVER"; break;
    default: out << "CDPOverwrite:unknown"; break;
  }
  return out;
}

ProofGenerator::ProofGenerator() {}

ProofGenerator::~ProofGenerator() {}

std::shared_ptr<ProofNode> ProofGenerator::getProofFor(Node f)
{
  Unreachable() << "ProofGenerator::getProofFor: " << identify()
                << " has no implementation" << std::endl;
  return nullptr;
}

bool ProofGenerator::addProofTo(Node f,
                                CDProof* pf,
                                CDPOverwrite opolicy,
                                bool doCopy)
{
  Trace("pfgen") << "ProofGenerator::addProofTo: " << f << "..." << std::endl;
  Assert(pf != nullptr);
  // plug in the proof provided by the generator, if it exists
  std::shared_ptr<ProofNode> apf = getProofFor(f);
  if (apf != nullptr)
  {
    Trace("pfgen") << "...got proof " << *apf.get() << std::endl;
    if (pf->addProof(apf, opolicy, doCopy))
    {
      Trace("pfgen") << "...success!" << std::endl;
      return true;
    }
    Trace("pfgen") << "...failed to add proof" << std::endl;
  }
  else
  {
    Trace("pfgen") << "...failed, no proof" << std::endl;
    Assert(false) << "Failed to get proof from generator for fact " << f;
  }
  return false;
}

}  // namespace cvc5::internal
