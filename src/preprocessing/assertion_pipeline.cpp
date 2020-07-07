/*********************                                                        */
/*! \file assertion_pipeline.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Justin Xu, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief AssertionPipeline stores a list of assertions modified by
 ** preprocessing passes
 **/

#include "preprocessing/assertion_pipeline.h"

#include "expr/node_manager.h"
#include "proof/proof.h"
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
      d_pnm(nullptr)
{
}

void AssertionPipeline::clear()
{
  d_nodes.clear();
  d_realAssertionsEnd = 0;
  d_assumptionsStart = 0;
  d_numAssumptions = 0;
  d_pfNodeStack.clear();
}

void AssertionPipeline::push_back(Node n, bool isAssumption, ProofGenerator* pgen)
{
  d_nodes.push_back(n);
  if (isAssumption)
  {
    Assert (pgen==nullptr);
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
  else if (options::proofNew())
  {
    size_t i = d_nodes.size() - 1;
    d_pfNodeStack[i].push_back(std::pair<Node,ProofGenerator*>(Node::null(), pgen));
  }
}

void AssertionPipeline::pushBackTrusted(theory::TrustNode trn)
{
  // push back what was proven
  push_back(trn.getProven(), false, trn.getGenerator());
}

void AssertionPipeline::replace(size_t i, Node n, ProofGenerator* pgen)
{
  PROOF(ProofManager::currentPM()->addDependence(n, d_nodes[i]););
  if (options::proofNew())
  {
    d_pfNodeStack[i].push_back(std::pair<Node,ProofGenerator*>(d_nodes[i], pgen));
  }
  d_nodes[i] = n;
}

void AssertionPipeline::replaceTrusted(size_t i, theory::TrustNode trn)
{
  Assert (trn.getKind()==theory::TrustNodeKind::REWRITE);
  Node n = trn.getNode();
  replace( i, n, trn.getGenerator());
}

void AssertionPipeline::replace(size_t i,
                                Node n,
                                const std::vector<Node>& addnDeps, ProofGenerator* pgen)
{
  PROOF(ProofManager::currentPM()->addDependence(n, d_nodes[i]);
        for (const auto& addnDep
             : addnDeps) {
          ProofManager::currentPM()->addDependence(n, addnDep);
        });
  if (options::proofNew())
  {
    d_pfNodeStack[i].push_back(std::pair<Node,ProofGenerator*>(d_nodes[i],pgen));
  }
  d_nodes[i] = n;
}

std::shared_ptr<ProofNode> AssertionPipeline::getProofFor(size_t i)
{
  std::map<size_t, std::vector<std::pair<Node,ProofGenerator*> > >::iterator it = d_pfNodeStack.find(i);
  if (it==d_pfNodeStack.end())
  {
    // could be an assumption, return nullptr
    return nullptr;
  }
  
  // for producing the final step
  it->second.push_back(std::pair<Node,ProofGenerator*>(d_nodes[i],nullptr));
  
  CDProof cdp(d_pnm);
  Node orig;
  Node prev;
  ProofGenerator* prevPg = nullptr;
  std::vector<Node> transChildren;
  for (const std::pair<Node,ProofGenerator*>& pr : it->second)
  {
    // we need to provide a proof of why the previous formula rewrote to the
    // current one, which is provided by the previous proof generator. If the
    // previous formula is null and we are on the second iteration of this loop,
    // then the previous proof generator has a proof of curr, which is the
    // original formula.
    Node curr = pr.first;
    orig = orig.isNull() ? curr : orig;
    
    if (prev.isNull())
    {
      if (!curr.isNull() && prevPg!=nullptr)
      {
        // a proof generator provided a proof for the original assertion
        Assert (orig==curr);
        std::shared_ptr<ProofNode> pfr = prevPg->getProofFor(orig);
        cdp.addProof(pfr);
      }
    }
    else
    {
      Node rewrite = prev.eqNode(curr);
      if (prevPg!=nullptr)
      {
        std::shared_ptr<ProofNode> pfr = prevPg->getProofFor(rewrite);
        cdp.addProof(pfr);
      }
      // possibly constructing a transitivity chain
      transChildren.push_back(rewrite);
    }
    
    prev = curr;
    prevPg = pr.second;
  }
  Assert (!orig.isNull());
  // prove ( orig == d_nodes[i] )
  Node fullRewrite = orig.eqNode(d_nodes[i]);
  if (transChildren.size()>=2)
  {
    cdp.addStep(fullRewrite, PfRule::TRANS, transChildren, {});
  }
  // prove d_nodes[i]
  cdp.addStep(d_nodes[i], PfRule::EQ_RESOLVE, {orig, fullRewrite}, {});
  
  // undo the change
  it->second.pop_back();
  
  return cdp.getProofFor(d_nodes[i]);
}

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

void AssertionPipeline::addSubstitutionNode(Node n)
{
  Assert(d_storeSubstsInAsserts);
  Assert(n.getKind() == kind::EQUAL);
  d_nodes[d_substsIndex] = theory::Rewriter::rewrite(
      NodeManager::currentNM()->mkNode(kind::AND, n, d_nodes[d_substsIndex]));
  Assert(theory::Rewriter::rewrite(d_nodes[d_substsIndex])
         == d_nodes[d_substsIndex]);
}

}  // namespace preprocessing
}  // namespace CVC4
