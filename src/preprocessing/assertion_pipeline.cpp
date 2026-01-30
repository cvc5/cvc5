/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
#include "smt/logic_exception.h"
#include "smt/preprocess_proof_generator.h"
#include "theory/builtin/proof_checker.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace preprocessing {

AssertionPipeline::AssertionPipeline(Env& env)
    : EnvObj(env),
      d_storeSubstsInAsserts(false),
      d_pppg(nullptr),
      d_conflict(false),
      d_isRefutationUnsound(false),
      d_isModelUnsound(false),
      d_isNegated(false)
{
  d_false = nodeManager()->mkConst(false);
}

void AssertionPipeline::clear()
{
  d_conflict = false;
  d_isRefutationUnsound = false;
  d_isModelUnsound = false;
  d_isNegated = false;
  d_nodes.clear();
  d_iteSkolemMap.clear();
  d_substsIndices.clear();
}

void AssertionPipeline::push_back(
    Node n, bool isInput, ProofGenerator* pgen, TrustId trustId, bool ensureRew)
{
  if (d_conflict)
  {
    // if we are already in conflict, we skip. This is required to handle the
    // case where "false" was already seen as an input assertion.
    return;
  }
  // If proof enabled, notify the preprocess proof generator.
  // Note that if n is (and F1 ... Fn), below we instead add the assertions
  // F1 .... Fn whose proofs are AND_ELIM steps given a proof of n. We do not
  // add n as an assertion. However, we also remember the proof for n itself.
  // The reason is that in rare cases we may relearn n (say via rewriting
  // another assumption) which may lead to a cyclic proof if that rewriting
  // depended on one of F1 ... Fn.
  if (isProofEnabled())
  {
    if (!isInput)
    {
      // notice this is always called, regardless of whether pgen is nullptr
      d_pppg->notifyNewAssert(n, pgen, trustId);
    }
    else
    {
      Assert(pgen == nullptr);
      // n is an input assertion, whose proof should be ASSUME.
      d_pppg->notifyInput(n);
    }
  }
  if (n == d_false)
  {
    markConflict();
  }
  else if (n.getKind() == Kind::AND)
  {
    // Immediately miniscope top-level AND, which is important for minimizing
    // dependencies in proofs. We add each conjunct seperately, justifying
    // each with an AND_ELIM step.
    std::vector<Node> conjs;
    if (isProofEnabled())
    {
      if (!isInput)
      {
        Assert(pgen != nullptr || trustId != TrustId::UNKNOWN_PREPROCESS_LEMMA);
        d_andElimEpg->addLazyStep(n, pgen, trustId);
      }
    }
    std::vector<Node> toProcess;
    toProcess.emplace_back(n);
    do
    {
      Node nc = toProcess.back();
      toProcess.pop_back();
      if (nc.getKind() == Kind::AND)
      {
        if (isProofEnabled())
        {
          NodeManager* nm = nodeManager();
          for (size_t j = 0, nchild = nc.getNumChildren(); j < nchild; j++)
          {
            size_t jj = (nchild-1)-j;
            Node in = nm->mkConstInt(Rational(jj));
            // Never overwrite here. This is because the assumption we would
            // overwrite might be at a lower user context. Overwriting the
            // assumption can lead to open proofs in incremental mode.
            d_andElimEpg->addStep(nc[jj],
                                  ProofRule::AND_ELIM,
                                  {nc},
                                  {in},
                                  false,
                                  CDPOverwrite::NEVER);
            toProcess.emplace_back(nc[jj]);
          }
        }
        else
        {
          toProcess.insert(toProcess.end(), nc.rbegin(), nc.rend());
        }
      }
      else
      {
        conjs.emplace_back(nc);
      }
    } while (!toProcess.empty());
    // add each conjunct
    for (const Node& nc : conjs)
    {
      push_back(nc,
                false,
                d_andElimEpg.get(),
                TrustId::UNKNOWN_PREPROCESS_LEMMA,
                ensureRew);
    }
    return;
  }
  else
  {
    d_nodes.push_back(n);
    if (ensureRew)
    {
      ensureRewritten(d_nodes.size() - 1);
    }
  }
  Trace("assert-pipeline") << "Assertions: ...new assertion " << n
                           << ", isInput=" << isInput << std::endl;
}

void AssertionPipeline::pushBackTrusted(TrustNode trn,
                                        TrustId trustId,
                                        bool ensureRew)
{
  Assert(trn.getKind() == TrustNodeKind::LEMMA);
  // push back what was proven
  push_back(trn.getProven(), false, trn.getGenerator(), trustId, ensureRew);
}

void AssertionPipeline::replace(size_t i,
                                Node n,
                                ProofGenerator* pgen,
                                TrustId trustId)
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
    Assert(pgen != nullptr || trustId != TrustId::UNKNOWN_PREPROCESS);
    d_pppg->notifyPreprocessed(d_nodes[i], n, pgen, trustId);
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

void AssertionPipeline::replaceTrusted(size_t i, TrustNode trn, TrustId trustId)
{
  Assert(i < d_nodes.size());
  if (trn.isNull())
  {
    // null trust node denotes no change, nothing to do
    return;
  }
  Assert(trn.getKind() == TrustNodeKind::REWRITE);
  Assert(trn.getProven()[0] == d_nodes[i]);
  replace(i, trn.getNode(), trn.getGenerator(), trustId);
}

void AssertionPipeline::ensureRewritten(size_t i)
{
  Assert(i < d_nodes.size());
  replace(i, rewrite(d_nodes[i]), d_rewpg.get());
}

void AssertionPipeline::enableProofs(smt::PreprocessProofGenerator* pppg)
{
  d_pppg = pppg;
  if (d_andElimEpg == nullptr)
  {
    d_andElimEpg.reset(
        new LazyCDProof(d_env, nullptr, userContext(), "AssertionsAndElim"));
  }
  if (d_rewpg == nullptr)
  {
    d_rewpg.reset(new RewriteProofGenerator(d_env));
  }
}

bool AssertionPipeline::isProofEnabled() const { return d_pppg != nullptr; }

void AssertionPipeline::enableStoreSubstsInAsserts()
{
  d_storeSubstsInAsserts = true;
  d_nodes.push_back(nodeManager()->mkConst<bool>(true));
}

void AssertionPipeline::disableStoreSubstsInAsserts()
{
  d_storeSubstsInAsserts = false;
}

void AssertionPipeline::addSubstitutionNode(Node n,
                                            ProofGenerator* pg,
                                            TrustId trustId)
{
  Assert(d_storeSubstsInAsserts);
  Assert(n.getKind() == Kind::EQUAL);
  size_t prevNodeSize = d_nodes.size();
  // ensure rewritten here
  push_back(n, false, pg, trustId, true);
  // remember this is a substitution index
  for (size_t i = prevNodeSize, newSize = d_nodes.size(); i < newSize; i++)
  {
    d_substsIndices.insert(i);
  }
}

bool AssertionPipeline::isSubstsIndex(size_t i) const
{
  return d_storeSubstsInAsserts
         && d_substsIndices.find(i) != d_substsIndices.end();
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
