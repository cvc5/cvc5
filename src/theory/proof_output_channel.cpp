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

ProofOutputChannel::ProofOutputChannel(OutputChannel& out,
                                       context::UserContext* u)
    : d_out(out), d_lemPfGen(u)
{
}
void ProofOutputChannel::conflict(Node conf, ProofGenerator* pfg)
{
  Node ckey = getConflictKeyValue(conf);
  // may or may not have supplied a generator
  if (pfg!=nullptr)
  {
    d_lemPfGen[ckey] = pfg;
  }
  d_out.conflict(conf);
}

std::shared_ptr<ProofNode> ProofOutputChannel::getProofForConflict(Node conf)
{
  Node ckey = getConflictKeyValue(conf);
  return getProof(ckey);
}

LemmaStatus ProofOutputChannel::lemma(Node lem,
                                      ProofGenerator* pfg,
                                      bool removable,
                                      bool preprocess,
                                      bool sendAtoms)
{
  Node lkey = getLemmaKeyValue(lem);
  // may or may not have supplied a generator
  if (pfg!=nullptr)
  {
    d_lemPfGen[lkey] = pfg;
  }
  return d_out.lemma(lem, removable, preprocess, sendAtoms);
}

std::shared_ptr<ProofNode> ProofOutputChannel::getProofForLemma(Node lem)
{
  Node lkey = getLemmaKeyValue(lem);
  return getProof(lkey);
}

std::shared_ptr<ProofNode> ProofOutputChannel::getProof(Node key) const
{
  NodeProofGenMap::const_iterator it = d_lemPfGen.find(key);
  if(it == d_lemPfGen.end())
  {
    Assert(false)
        << "ProofOutputChannel::getProof: no generator provided for " << key
        << std::endl;
    return nullptr;
  }
  std::shared_ptr<ProofNode> ret = (*it).second->getProof(key);
  Assert(ret != nullptr)
      << "ProofOutputChannel::getProof: could not generate proof for " << key
      << std::endl;
  return ret;
}

Node ProofOutputChannel::getConflictKeyValue(Node conf)
{
  return conf.negate();
}

Node ProofOutputChannel::getLemmaKeyValue(Node lem) { return lem; }

void ProofOutputChannel::requirePhase(TNode n, bool phase)
{
  d_out.requirePhase(n, phase);
}

void ProofOutputChannel::setIncomplete()
{
  d_out.setIncomplete();
}

}  // namespace theory
}  // namespace CVC4
