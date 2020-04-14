/*********************                                                        */
/*! \file proof_output_channel.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The Evaluator class
 **
 ** The Evaluator class.
 **/

#include "theory/proof_output_channel.h"

namespace CVC4 {
namespace theory {

std::shared_ptr<ProofNode> ProofGenerator::getProofForLemma(Node lem)
{
  // no implementation
  return nullptr;
}

ProofOutputChannel::ProofOutputChannel(OutputChannel& out,
                                       context::UserContext* u)
    : d_out(out), d_lemmaProofGen(u)
{
}

void ProofOutputChannel::lemma(Node lem,
                               ProofGenerator* pfg,
                               bool removable,
                               bool preprocess,
                               bool sendAtoms)
{
  Assert(pfg != nullptr);
  d_out.lemma(lem, removable, preprocess, sendAtoms);
  d_lemmaProofGen[lem] = pfg;
}

std::shared_ptr<ProofNode> ProofOutputChannel::getProofForLemma(Node lem) const
{
  NodeProofGenMap::const_iterator it = d_lemmaProofGen.find(lem);
  Assert(it != d_lemmaProofGen.end());
  std::shared_ptr<ProofNode> ret = (*it).second->getProofForLemma(lem);
  Assert(ret != nullptr)
      << "ProofOutputChannel::getProofForLemma: could not generate proof for "
      << lem << std::endl;
  return ret;
}

}  // namespace theory
}  // namespace CVC4
