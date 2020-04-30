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
                                                   LazyCDProof* lpf)
    : EngineOutputChannel(engine, theory), d_lazyPf(lpf)
{
}
void ProofEngineOutputChannel::trustedConflict(TrustNode pconf)
{
  Assert(pconf.getKind() == TrustNodeKind::CONFLICT);
  Node conf = pconf.getNode();
  ProofGenerator* pfg = pconf.getGenerator();
  // may or may not have supplied a generator
  if (pfg != nullptr)
  {
    Node ckey = getConflictKeyValue(conf);
    // if we have, add it to the lazy proof object
    d_lazyPf->addStep(ckey, pfg);
    Assert(pfg->hasProofFor(ckey));
  }
  // now, call the normal interface to conflict
  conflict(conf);
}

LemmaStatus ProofEngineOutputChannel::trustedLemma(TrustNode plem,
                                                   bool removable,
                                                   bool preprocess,
                                                   bool sendAtoms)
{
  Assert(plem.getKind() == TrustNodeKind::LEMMA);
  TNode lem = plem.getNode();
  ProofGenerator* pfg = plem.getGenerator();
  // may or may not have supplied a generator
  if (pfg != nullptr)
  {
    Node lkey = getLemmaKeyValue(lem);
    // if we have, add it to the lazy proof object
    d_lazyPf->addStep(lkey, pfg);
    Assert(pfg->hasProofFor(lkey));
  }
  // now, call the normal interface for lemma
  return OutputChannel::lemma(lem, removable, preprocess, sendAtoms);
}

Node ProofEngineOutputChannel::getConflictKeyValue(Node conf)
{
  return conf.negate();
}

Node ProofEngineOutputChannel::getLemmaKeyValue(Node lem) { return lem; }

}  // namespace theory
}  // namespace CVC4
