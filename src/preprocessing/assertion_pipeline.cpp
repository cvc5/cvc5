/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * AssertionPipeline stores a list of assertions modified by
 * preprocessing passes.
 */

#include "preprocessing/assertion_pipeline.h"

#include "expr/node_manager.h"
#include "options/smt_options.h"
#include "proof/lazy_proof.h"
#include "smt/preprocess_proof_generator.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5::internal {
namespace preprocessing {

AssertionPipeline::AssertionPipeline(Env& env)
    : EnvObj(env),
      d_storeSubstsInAsserts(false),
      d_substsIndex(0),
      d_pppg(nullptr)
{
}

void AssertionPipeline::clear()
{
  d_nodes.clear();
  d_iteSkolemMap.clear();
}

void AssertionPipeline::push_back(Node n,
                                  bool isInput,
                                  ProofGenerator* pgen)
{
  d_nodes.push_back(n);
  Trace("assert-pipeline") << "Assertions: ...new assertion " << n
                           << ", isInput=" << isInput << std::endl;
  if (isProofEnabled())
  {
    if (!isInput)
    {
      // notice this is always called, regardless of whether pgen is nullptr
      d_pppg->notifyNewAssert(n, pgen);
    }
    else
    {
      Assert(pgen == nullptr);
      // n is an input assertion, whose proof should be ASSUME.
      d_pppg->notifyInput(n);
    }
  }
}

void AssertionPipeline::pushBackTrusted(TrustNode trn)
{
  Assert(trn.getKind() == TrustNodeKind::LEMMA);
  // push back what was proven
  push_back(trn.getProven(), false, trn.getGenerator());
}

void AssertionPipeline::replace(size_t i, Node n, ProofGenerator* pgen)
{
  if (n == d_nodes[i])
  {
    // no change, skip
    return;
  }
  Trace("assert-pipeline") << "Assertions: Replace " << d_nodes[i] << " with "
                           << n << std::endl;
  if (isProofEnabled())
  {
    d_pppg->notifyPreprocessed(d_nodes[i], n, pgen);
  }
  d_nodes[i] = n;
}

void AssertionPipeline::replaceTrusted(size_t i, TrustNode trn)
{
  if (trn.isNull())
  {
    // null trust node denotes no change, nothing to do
    return;
  }
  Assert(trn.getKind() == TrustNodeKind::REWRITE);
  Assert(trn.getProven()[0] == d_nodes[i]);
  replace(i, trn.getNode(), trn.getGenerator());
}

void AssertionPipeline::enableProofs(smt::PreprocessProofGenerator* pppg)
{
  d_pppg = pppg;
}

bool AssertionPipeline::isProofEnabled() const { return d_pppg != nullptr; }

void AssertionPipeline::enableStoreSubstsInAsserts()
{
  d_storeSubstsInAsserts = true;
  d_substsIndex = d_nodes.size();
  d_nodes.push_back(NodeManager::currentNM()->mkConst<bool>(true));
}

void AssertionPipeline::disableStoreSubstsInAsserts()
{
  d_storeSubstsInAsserts = false;
}

void AssertionPipeline::addSubstitutionNode(Node n, ProofGenerator* pg)
{
  Assert(d_storeSubstsInAsserts);
  Assert(n.getKind() == kind::EQUAL);
  conjoin(d_substsIndex, n, pg);
}

void AssertionPipeline::conjoin(size_t i, Node n, ProofGenerator* pg)
{
  NodeManager* nm = NodeManager::currentNM();
  Node newConj = nm->mkNode(kind::AND, d_nodes[i], n);
  Node newConjr = rewrite(newConj);
  Trace("assert-pipeline") << "Assertions: conjoin " << n << " to "
                           << d_nodes[i] << std::endl;
  Trace("assert-pipeline-debug") << "conjoin " << n << " to " << d_nodes[i]
                                 << ", got " << newConjr << std::endl;
  if (newConjr == d_nodes[i])
  {
    // trivial, skip
    return;
  }
  if (isProofEnabled())
  {
    if (newConjr == n)
    {
      // don't care about the previous proof and can simply plug in the
      // proof from pg if the resulting assertion is the same as n.
      d_pppg->notifyNewAssert(newConjr, pg);
    }
    else
    {
      // ---------- from pppg   --------- from pg
      // d_nodes[i]                n
      // -------------------------------- AND_INTRO
      //      d_nodes[i] ^ n
      // -------------------------------- MACRO_SR_PRED_TRANSFORM
      //   rewrite( d_nodes[i] ^ n )
      // allocate a fresh proof which will act as the proof generator
      LazyCDProof* lcp = d_pppg->allocateHelperProof();
      lcp->addLazyStep(n, pg, PfRule::PREPROCESS);
      if (d_nodes[i].isConst() && d_nodes[i].getConst<bool>())
      {
        // skip the AND_INTRO if the previous d_nodes[i] was true
        newConj = n;
      }
      else
      {
        lcp->addLazyStep(d_nodes[i], d_pppg);
        lcp->addStep(newConj, PfRule::AND_INTRO, {d_nodes[i], n}, {});
      }
      if (!CDProof::isSame(newConjr, newConj))
      {
        lcp->addStep(
            newConjr, PfRule::MACRO_SR_PRED_TRANSFORM, {newConj}, {newConjr});
      }
      // Notice we have constructed a proof of a new assertion, where d_pppg
      // is referenced in the lazy proof above. If alternatively we had
      // constructed a proof of d_nodes[i] = rewrite( d_nodes[i] ^ n ), we would
      // have used notifyPreprocessed. However, it is simpler to make the
      // above proof.
      d_pppg->notifyNewAssert(newConjr, lcp);
    }
  }
  d_nodes[i] = newConjr;
  Assert(rewrite(newConjr) == newConjr);
}

}  // namespace preprocessing
}  // namespace cvc5::internal
