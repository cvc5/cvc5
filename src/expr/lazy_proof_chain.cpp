/*********************                                                        */
/*! \file lazy_proof_chain.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of lazy proof utility
 **/

#include "expr/lazy_proof_chain.h"

#include "expr/proof_node_algorithm.h"
#include "options/smt_options.h"

namespace CVC4 {

LazyCDProofChain::LazyCDProofChain(ProofNodeManager* pnm,
                                   context::Context* c,
                                   std::string name)
    : CDProof(pnm, c, name), d_gens(c ? c : &d_context)
{
}

LazyCDProofChain::~LazyCDProofChain() {}

std::shared_ptr<ProofNode> LazyCDProofChain::getProofFor(Node fact)
{
  Trace("lazy-cdproofchain")
      << "LazyCDProofChain::getProofFor " << fact << "\n";
  // which facts have had proofs retrieved for. This is maintained to avoid
  // cycles. It also saves the proof node of the fact and its proof node
  // assumptions in the map's range
  std::unordered_map<
      Node,
      std::pair<std::shared_ptr<ProofNode>,
                std::unordered_map<Node,
                                   std::vector<std::shared_ptr<ProofNode>>,
                                   NodeHashFunction>>,
      NodeHashFunction>
      expandedToConnect;
  std::unordered_map<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      expanded;
  std::vector<Node> visit{fact};
  std::unordered_map<Node, Node, NodeHashFunction> visited;
  Node cur;

  do
  {
    cur = visit.back();
    visit.pop_back();
    const auto itVisited = visited.find(cur);
    // pre-traversal
    if (itVisited == visited.end())
    {
      Trace("lazy-cdproofchain")
          << "LazyCDProofChain::getProofFor: check " << cur << "\n";
      if (!hasGenerator(cur))
      {
        Trace("lazy-cdproofchain")
            << "LazyCDProofChain::getProofFor: nothing to do\n";
        // nothing to do for this fact, it'll be a leaf in the final proof node
        visited[cur] = cur;
        continue;
      }
      // retrive its proof node
      bool isSym = false;
      ProofGenerator* pg = getGeneratorFor(cur, isSym);
      Assert(pg != nullptr);
      Trace("lazy-cdproofchain")
          << "LazyCDProofChain::getProofFor: Call generator " << pg->identify()
          << " for chain link " << cur << "\n";
      Node curFactGen = isSym ? CDProof::getSymmFact(cur) : cur;
      // copy the proof node so that changing it does not change the stored one
      std::shared_ptr<ProofNode> curPfn = pg->getProofFor(curFactGen)->clone();
      if (isSym)
      {
        curPfn = d_manager->mkNode(PfRule::SYMM, {curPfn}, {});
      }
      Trace("lazy-cdproofchain-debug")
          << "LazyCDProofChain::getProofFor: stored proof: " << *curPfn.get()
          << "\n";
      // retrieve free assumptions and their respective proof nodes
      std::map<Node, std::vector<ProofNode*>> famap;
      expr::getFreeAssumptionsMap(curPfn.get(), famap);
      if (Trace.isOn("lazy-cdproofchain"))
      {
        Trace("lazy-cdproofchain")
            << "LazyCDProofChain::getProofFor: free assumptions:\n";
        for (auto fap : famap)
        {
          Trace("lazy-cdproofchain")
              << "LazyCDProofChain::getProofFor:  - " << fap.first << "\n";
        }
      }
      Trace("lazy-cdproofchain") << push;
      Trace("lazy-cdproofchain-debug") << push;
      // mark for future connection, when free assumptions that are chain links
      // must have been expanded and connected
      visited[cur] = Node::null();
      visit.push_back(cur);
      // use a persistent version of the free assumptions to proof nodes map
      std::unordered_map<Node,
                         std::vector<std::shared_ptr<ProofNode>>,
                         NodeHashFunction>
          famapPersistent;
      // enqueue free assumptions to process and register proof nodes to be
      // connected
      for (const std::pair<const Node, std::vector<ProofNode*>>& fap : famap)
      {
        // check cycles
        AlwaysAssert(expandedToConnect.find(fap.first)
                     == expandedToConnect.end())
            << "Fact " << fap.first << " is part of a cycle\n";
        visit.push_back(fap.first);
        std::vector<std::shared_ptr<ProofNode>> pfns;
        for (ProofNode* pfn : fap.second)
        {
          pfns.push_back(pfn->clone());
        }
        famapPersistent[fap.first] = pfns;
      }
      // map node whose proof node must be expanded to the respective poof node
      // and to the persistent map of its assumptions to proof nodes
      expandedToConnect[cur] =
          std::pair<std::shared_ptr<ProofNode>,
                    std::unordered_map<Node,
                                       std::vector<std::shared_ptr<ProofNode>>,
                                       NodeHashFunction>>(curPfn,
                                                          famapPersistent);
    }
    // post-traversal
    else if (itVisited->second.isNull())
    {
      Trace("lazy-cdproofchain") << pop;
      Trace("lazy-cdproofchain-debug") << pop;
      Trace("lazy-cdproofchain") << "LazyCDProofChain::getProofFor: "
                                    "connect proofs for assumptions of: "
                                 << cur << "\n";
      // mark final processing
      visited[cur] = cur;
      // get proof nodes
      auto it = expandedToConnect.find(cur);
      Assert(it != expandedToConnect.end());
      // the first element of the iterator pair is the proofNode of cur, the
      // second is the map of the assumption node to all its proofnodes
      for (const std::pair<const Node, std::vector<std::shared_ptr<ProofNode>>>&
               fap : it->second.second)
      {
        // see if assumption has been expanded and thus has a new proof node to
        // connect here
        auto itt = expanded.find(fap.first);
        if (itt == expanded.end())
        {
          Trace("lazy-cdproofchain")
              << "LazyCDProofChain::getProofFor: assumption " << fap.first
              << " not expanded\n";
          continue;
        }
        Trace("lazy-cdproofchain")
            << "LazyCDProofChain::getProofFor: assumption " << fap.first
            << " expanded\n";
        // update each assumption proof node with the expanded proof node of
        // that assumption
        for (std::shared_ptr<ProofNode> pfn : fap.second)
        {
          d_manager->updateNode(pfn.get(), itt->second.get());
        }
      }
      // assign the expanded proof node
      expanded[cur] = it->second.first;
      Trace("lazy-cdproofchain-debug")
          << "LazyCDProofChain::getProofFor: expanded proof node: "
          << *it->second.first.get() << "\n";
    }
  } while (!visit.empty());
  Assert(expanded.find(cur) != expanded.end());
  // final proof of fact
  return expanded[cur];
}

void LazyCDProofChain::addLazyStep(Node expected,
                                   ProofGenerator* pg,
                                   const char* ctx)
{
  Assert(pg != nullptr);
  Trace("lazy-cdproofchain") << "LazyCDProofChain::addLazyStep: " << expected
                             << " set to generator " << pg->identify() << "\n";
  if (d_gens.find(expected) != d_gens.end())
  {
    Trace("lazy-cdproofchain") << "LazyCDProofChain::addLazyStep: " << expected
                               << " had a previous generator\n";
  }
  d_gens.insert(expected, pg);
  // check if chain is closed if options::proofNewEagerChecking() is on
  if (options::proofNewEagerChecking())
  {
    Trace("lazy-cdproofchain")
        << "LazyCDProofChain::addLazyStep: Checking closed proof...\n";
    std::shared_ptr<ProofNode> pfn = getProofFor(expected);
    std::vector<Node> allowedLeaves{d_fixedAssumptions.begin(),
                                    d_fixedAssumptions.end()};
    for (const std::pair<const Node, ProofGenerator*>& link : d_gens)
    {
      allowedLeaves.push_back(link.first);
    }
    if (Trace.isOn("lazy-cdproofchain"))
    {
      Trace("lazy-cdproofchain") << "Checking relative to leaves...\n";
      for (const Node& n : allowedLeaves)
      {
        Trace("lazy-cdproofchain") << "  - " << n << "\n";
      }
      Trace("lazy-cdproofchain") << "\n";
    }
    pfnEnsureClosedWrt(pfn.get(), allowedLeaves, "lazy-cdproofchain", ctx);
  }
}

bool LazyCDProofChain::hasGenerator(Node fact) const
{
  NodeProofGeneratorMap::const_iterator it = d_gens.find(fact);
  if (it != d_gens.end())
  {
    return true;
  }
  // maybe there is a symmetric fact?
  Node factSym = CDProof::getSymmFact(fact);
  if (!factSym.isNull())
  {
    it = d_gens.find(factSym);
  }
  return it != d_gens.end();
}

ProofGenerator* LazyCDProofChain::getGeneratorFor(Node fact, bool& isSym)
{
  isSym = false;
  NodeProofGeneratorMap::const_iterator it = d_gens.find(fact);
  if (it != d_gens.end())
  {
    return (*it).second;
  }
  Node factSym = CDProof::getSymmFact(fact);
  // could be symmetry
  if (factSym.isNull())
  {
    // can't be symmetry, return the default generator
    return nullptr;
  }
  it = d_gens.find(factSym);
  if (it != d_gens.end())
  {
    isSym = true;
    return (*it).second;
  }
  return nullptr;
}

void LazyCDProofChain::addFixedAssumption(Node assumption)
{
  Trace("lazy-cdproofchain")
      << "LazyCDProofChain::addFixedAssumption " << assumption << "\n";
  d_fixedAssumptions.push_back(assumption);
}

void LazyCDProofChain::addFixedAssumptions(const std::vector<Node>& assumptions)
{
  if (Trace.isOn("lazy-cdproofchain"))
  {
    for (const Node& a : assumptions)
    {
      Trace("lazy-cdproofchain")
          << "LazyCDProofChain::addFixedAssumptions: - " << a << "\n";
    }
  }
  d_fixedAssumptions.insert(
      d_fixedAssumptions.end(), assumptions.begin(), assumptions.end());
}

}  // namespace CVC4
