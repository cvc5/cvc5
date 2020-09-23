/*********************                                                        */
/*! \file assertion_pipeline.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief AssertionPipeline stores a list of assertions modified by
 ** preprocessing passes
 **/

#include "preprocessing/assertion_pipeline.h"

#include "expr/node_manager.h"
#include "options/smt_options.h"
#include "proof/proof_manager.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {

AssertionPipeline::AssertionPipeline()
    : d_realAssertionsEnd(0),
      d_storeSubstsInAsserts(false),
      d_substsIndex(0),
      d_assumptionsStart(0),
      d_numAssumptions(0),
      d_pppg(nullptr)
{
}

void AssertionPipeline::clear()
{
  d_nodes.clear();
  d_realAssertionsEnd = 0;
  d_assumptionsStart = 0;
  d_numAssumptions = 0;
}

void AssertionPipeline::push_back(Node n,
                                  bool isAssumption,
                                  bool isInput,
                                  ProofGenerator* pgen)
{
  d_nodes.push_back(n);
  if (isAssumption)
  {
    Assert(pgen == nullptr);
    if (d_numAssumptions == 0)
    {
      d_assumptionsStart = d_nodes.size() - 1;
    }
    // Currently, we assume that assumptions are all added one after another
    // and that we store them in the same vector as the assertions. Once we
    // split the assertions up into multiple vectors (see issue #2473), we will
    // not have this limitation anymore.
    Assert(d_assumptionsStart + d_numAssumptions == d_nodes.size() - 1);
    d_numAssumptions++;
  }
  if (isProofEnabled())
  {
    if (!isInput)
    {
      // notice this is always called, regardless of whether pgen is nullptr
      d_pppg->notifyNewAssert(n, pgen);
    }
    else
    {
      Trace("smt-pppg") << "...input assertion " << n << std::endl;
    }
  }
}

void AssertionPipeline::pushBackTrusted(theory::TrustNode trn)
{
  Assert(trn.getKind() == theory::TrustNodeKind::LEMMA);
  // push back what was proven
  push_back(trn.getProven(), false, false, trn.getGenerator());
}

void AssertionPipeline::replace(size_t i, Node n, ProofGenerator* pgen)
{
  if (n == d_nodes[i])
  {
    // no change, abort
    // TODO: make assertion failure?
    return;
  }
  Trace("smt-pppg-repl") << "Replace " << d_nodes[i] << " with " << n
                         << std::endl;
  // NOTE: checks for replacing true with something (should use conjoin instead)
  // Assert(!d_nodes[i].isConst());
  if (options::unsatCores())
  {
    ProofManager::currentPM()->addDependence(n, d_nodes[i]);
  }
  if (isProofEnabled())
  {
    d_pppg->notifyPreprocessed(d_nodes[i], n, pgen);
  }
  d_nodes[i] = n;
}

void AssertionPipeline::replaceTrusted(size_t i, theory::TrustNode trn)
{
  Assert(trn.getKind() == theory::TrustNodeKind::REWRITE);
  replace(i, trn.getNode(), trn.getGenerator());
}

void AssertionPipeline::setProofGenerator(smt::PreprocessProofGenerator* pppg)
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
  if (n == d_nodes[i])
  {
    // trivial case, skip to avoid cyclic proofs below
    return;
  }
  Node newConj = NodeManager::currentNM()->mkNode(kind::AND, n, d_nodes[i]);
  Node newConjr = theory::Rewriter::rewrite(newConj);
  if (isProofEnabled())
  {
    /*
    LazyCDProof lcp(d_pppg->getManager());
    lcp.addLazyStep(n, pgen);
    lcp.addLazyStep(d_nodes[i], d_pppg);
    lcp.addStep(newConj, PfRule::AND_INTRO, {n, d_nodes[i]}, {});
    if (newConj!=newConjr)
    {
      lcp.addStep(newConjr, PfRule::MACRO_SR_PRED_TRANSFORM, {newConj},
    {newConjr});
    }
    std::shared_ptr<ProofNode> pf = lcp.getProofFor(newConjr);
    theory::EagerProofGenerator * helper = d_pppg->getHelperProofGenerator();
    helper->setProofFor(newConjr, pf);
    */

    ProofGenerator* pgReplace = nullptr;  // d_pppg->getHelperProofGenerator();
    // TODO
    // d_pppg->notifyNewAssert(n, pgen);
    d_pppg->notifyPreprocessed(d_nodes[i], newConjr, pgReplace);
  }
  if (options::unsatCores())
  {
    ProofManager::currentPM()->addDependence(newConjr, d_nodes[i]);
  }
  d_nodes[i] = newConjr;
  Assert(theory::Rewriter::rewrite(newConjr) == newConjr);
}

}  // namespace preprocessing
}  // namespace CVC4
