/*********************                                                        */
/*! \file proof_engine_output_channel.cpp
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

#include "theory/proof_engine_output_channel.h"

namespace CVC4 {
namespace theory {

ProofEngineOutputChannel::ProofEngineOutputChannel(TheoryEngine* engine,
                                                   theory::TheoryId theory,
                                                   context::UserContext* u)
    : EngineOutputChannel(engine, theory), d_outPfGen(u)
{
}
void ProofEngineOutputChannel::trustedConflict(TrustNode pconf)
{
  Assert(pconf.getKind() == TrustNodeKind::CONFLICT);
  Node conf = pconf.getNode();
  ProofGenerator* pfg = pconf.getGenerator();
  Node ckey = getConflictKeyValue(conf);
  // may or may not have supplied a generator
  if (pfg != nullptr)
  {
    d_outPfGen[ckey] = pfg;
    Assert(pfg->hasProofFor(ckey));
  }
  // now, call conflict
  conflict(conf);
}

std::shared_ptr<ProofNode> ProofEngineOutputChannel::getProofForConflict(
    Node conf) const
{
  Node ckey = getConflictKeyValue(conf);
  ProofGenerator* pgen = getProofGeneratorForKey(ckey);
  if (pgen == nullptr)
  {
    return nullptr;
  }
  std::shared_ptr<ProofNode> ret = pgen->getProofFor(ckey);
  Assert(ret != nullptr)
      << "ProofEngineOutputChannel::getProofForConflict: could "
         "not generate proof for "
      << conf << std::endl;
  return ret;
}

LemmaStatus ProofEngineOutputChannel::trustedLemma(TrustNode plem,
                                                   bool removable,
                                                   bool preprocess,
                                                   bool sendAtoms)
{
  Assert(plem.getKind() == TrustNodeKind::LEMMA);
  TNode lem = plem.getNode();
  ProofGenerator* pfg = plem.getGenerator();
  Node lkey = getLemmaKeyValue(lem);
  // may or may not have supplied a generator
  if (pfg != nullptr)
  {
    d_outPfGen[lkey] = pfg;
    Assert(pfg->hasProofFor(lkey));
  }
  // now, call lemma
  return OutputChannel::lemma(lem, removable, preprocess, sendAtoms);
}

std::shared_ptr<ProofNode> ProofEngineOutputChannel::getProofForLemma(
    Node lem) const
{
  Node lkey = getLemmaKeyValue(lem);
  ProofGenerator* pgen = getProofGeneratorForKey(lkey);
  if (pgen == nullptr)
  {
    return nullptr;
  }
  std::shared_ptr<ProofNode> ret = pgen->getProofFor(lem);
  Assert(ret != nullptr)
      << "ProofEngineOutputChannel::getProofForLemma: could not "
         "generate proof for lemma "
      << lem << std::endl;
  return ret;
}

Node ProofEngineOutputChannel::getConflictKeyValue(Node conf)
{
  return conf.negate();
}

Node ProofEngineOutputChannel::getLemmaKeyValue(Node lem) { return lem; }

ProofGenerator* ProofEngineOutputChannel::getProofGeneratorForKey(
    Node key) const
{
  NodeProofGenMap::const_iterator it = d_outPfGen.find(key);
  if (it == d_outPfGen.end())
  {
    Assert(false) << "ProofEngineOutputChannel::getProofGeneratorForKey: no "
                     "generator provided for "
                  << key << std::endl;
    return nullptr;
  }
  return (*it).second;
}

}  // namespace theory
}  // namespace CVC4
