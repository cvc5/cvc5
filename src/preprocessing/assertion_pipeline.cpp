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
#include "util/rational.h"
#include "options/smt_options.h"
#include "proof/lazy_proof.h"
#include "smt/logic_exception.h"
#include "smt/preprocess_proof_generator.h"
#include "theory/builtin/proof_checker.h"

namespace cvc5::internal {
namespace preprocessing {

AssertionPipeline::AssertionPipeline(Env& env)
    : EnvObj(env),
      d_storeSubstsInAsserts(false),
      d_substsIndex(0),
      d_pppg(nullptr),
      d_conflict(false),
      d_isRefutationUnsound(false),
      d_isModelUnsound(false),
      d_isNegated(false)
{
  d_false = NodeManager::currentNM()->mkConst(false);
}

void AssertionPipeline::clear()
{
  d_conflict = false;
  d_isRefutationUnsound = false;
  d_isModelUnsound = false;
  d_isNegated = false;
  d_nodes.clear();
  d_iteSkolemMap.clear();
}

void AssertionPipeline::push_back(Node n,
                                  bool isInput,
                                  ProofGenerator* pgen)
{
  if (d_conflict)
  {
    // if we are already in conflict, we skip. This is required to handle the
    // case where "false" was already seen as an input assertion.
    return;
  }
  if (n == d_false)
  {
    markConflict();
  }
  else if (n.getKind()==Kind::AND)
  {
    if (isProofEnabled())
    {
      if (!isInput)
      {
        d_andElimEpg->addLazyStep(n, pgen, TrustId::PREPROCESS_LEMMA);
      }
      NodeManager * nm = NodeManager::currentNM();
      for (size_t i=0, nchild=n.getNumChildren(); i<nchild; i++)
      {
        Node in = nm->mkConstInt(Rational(i));
        d_andElimEpg->addStep(n[i], ProofRule::AND_ELIM, {n}, {in});
      }
    }
    for (const Node& nc : n)
    {
      push_back(nc, false, d_andElimEpg.get());
    }
    return;
  }
  else
  {
    d_nodes.push_back(n);
  }
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
  Assert(i < d_nodes.size());
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
  if (n == d_false)
  {
    markConflict();
  }
  else
  {
    d_nodes[i] = n;
  }
}

void AssertionPipeline::replaceTrusted(size_t i, TrustNode trn)
{
  Assert(i < d_nodes.size());
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
  if (d_andElimEpg==nullptr)
  {
    d_andElimEpg.reset(new LazyCDProof(d_env, nullptr, userContext(), "AssertionsAndElim"));
  }
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
  Assert(n.getKind() == Kind::EQUAL);
  push_back(n, false, pg);
}

void AssertionPipeline::markConflict()
{
  d_conflict = true;
  d_nodes.clear();
  d_iteSkolemMap.clear();
  d_nodes.push_back(d_false);
}

void AssertionPipeline::markRefutationUnsound()
{
  d_isRefutationUnsound = true;
}

void AssertionPipeline::markModelUnsound() { d_isModelUnsound = true; }

void AssertionPipeline::markNegated()
{
  if (d_isRefutationUnsound || d_isModelUnsound)
  {
    // disallow unintuitive uses of global negation.
    std::stringstream ss;
    ss << "Cannot negate the preprocessed assertions when already marked as "
          "refutation or model unsound.";
    throw LogicException(ss.str());
  }
  d_isNegated = true;
}

}  // namespace preprocessing
}  // namespace cvc5::internal
