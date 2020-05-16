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
  Node conf = pconf.getNode();
  if (d_lazyPf != nullptr)
  {
    Node ckey = pconf.getProven();
    ProofGenerator* pfg = pconf.getGenerator();
    // may or may not have supplied a generator
    if (pfg != nullptr)
    {
      ++d_statistics.trustedConflicts;
      // if we have, add it to the lazy proof object
      d_lazyPf->addLazyStep(ckey, pfg);
      Assert(pfg->hasProofFor(ckey));
    }
    else
    {
      // if none provided, do a very coarse-grained step
      addTheoryLemmaStep(ckey);
    }
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
  if (d_lazyPf != nullptr)
  {
    Node lkey = plem.getProven();
    ProofGenerator* pfg = plem.getGenerator();
    // may or may not have supplied a generator
    if (pfg != nullptr)
    {
      ++d_statistics.trustedLemmas;
      // if we have, add it to the lazy proof object
      d_lazyPf->addLazyStep(lkey, pfg);
      Assert(pfg->hasProofFor(lkey));
    }
    else
    {
      // if none provided, do a very coarse-grained step
      addTheoryLemmaStep(lkey);
    }
  }
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
