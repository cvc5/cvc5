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

#include "expr/lazy_proof.h"

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
  d_engine->processTrustNode(pconf, d_theory);
  TNode conf = pconf.getNode();
  // now, call the normal interface to conflict
  conflict(conf);
}

LemmaStatus ProofEngineOutputChannel::trustedLemma(TrustNode plem,
                                                   bool removable,
                                                   bool preprocess,
                                                   bool sendAtoms)
{
  Assert(plem.getKind() == TrustNodeKind::LEMMA);
  d_engine->processTrustNode(plem, d_theory);
  TNode lem = plem.getNode();
  // now, call the normal interface for lemma
  return OutputChannel::lemma(lem, removable, preprocess, sendAtoms);
}

bool ProofEngineOutputChannel::addTheoryLemmaStep(Node f)
{
  Assert(d_lazyPf != nullptr);
  Assert(!f.isNull());
  std::vector<Node> children;
  std::vector<Node> args;
  args.push_back(f);
  unsigned tid = static_cast<unsigned>(d_theory);
  Node tidn = NodeManager::currentNM()->mkConst(Rational(tid));
  args.push_back(tidn);
  // add the step, should always succeed;
  return d_lazyPf->addStep(f, PfRule::THEORY_LEMMA, children, args);
}

}  // namespace theory
}  // namespace CVC4
