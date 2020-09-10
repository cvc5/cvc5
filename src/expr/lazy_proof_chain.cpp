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
  // cycles. It also saves the proof node of the fact
  std::unordered_map<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      expandedToConnect;
  std::unordered_set<Node, NodeHashFunction> expanded;
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
      std::shared_ptr<ProofNode> curPfn = pg->getProofFor(curFactGen);
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
      // enqueue free assumptions to process
      for (const std::pair<const Node, std::vector<ProofNode*>>& fap : famap)
      {
        // check cycles, which are cases in which we have facts in
        // expandedToConnect but not already expanded
        auto it = expandedToConnect.find(fap.first);
        if (it != expandedToConnect.end() && !expanded.count(fap.first))
        {
          // mark as a not to expand assumption. We do this rather than just
          // assining visited[fap.first] to a non-null value so that we properly
          // pop the traces previously pushed.
          Trace("lazy-cdproofchain")
              << "LazyCDProofChain::getProofFor: removing cyclic assumption "
              << fap.first << " from expansion\n";
          expandedToConnect.erase(it);
          break;
        }
        // already expanded, skip
        if (expanded.count(fap.first))
        {
          continue;
        }
        visit.push_back(fap.first);
      }
      // map node whose proof node must be expanded to the respective poof node
      expandedToConnect[cur] = curPfn;
    }
    // post-traversal
    else if (itVisited->second.isNull())
    {
      Assert(!expanded.count(cur));
      Trace("lazy-cdproofchain") << pop;
      Trace("lazy-cdproofchain-debug") << pop;
      // mark final processing
      visited[cur] = cur;
      // get proof node to expand
      auto it = expandedToConnect.find(cur);
      // this was part of a cycle, ignore it
      if (it == expandedToConnect.end())
      {
        continue;
      }
      Trace("lazy-cdproofchain") << "LazyCDProofChain::getProofFor: "
                                    "connect proofs for assumptions of: "
                                 << cur << "\n";

      // get assumptions
      std::map<Node, std::vector<ProofNode*>> famap;
      expr::getFreeAssumptionsMap(it->second.get(), famap);
      // the first element of the iterator pair is the proofNode of cur, the
      // second is the map of the assumption node to all its proofnodes
      for (const std::pair<const Node, std::vector<ProofNode*>>& fap : famap)
      {
        // see if assumption has been expanded and thus has a new proof node to
        // connect here
        if (!expanded.count(fap.first))
        {
          Trace("lazy-cdproofchain")
              << "LazyCDProofChain::getProofFor: assumption " << fap.first
              << " not expanded\n";
          continue;
        }
        auto itt = expandedToConnect.find(fap.first);
        Assert(itt != expandedToConnect.end());
        Trace("lazy-cdproofchain")
            << "LazyCDProofChain::getProofFor: assumption " << fap.first
            << " expanded\n";
        Trace("lazy-cdproofchain-debug")
            << "LazyCDProofChain::getProofFor: expanded to: "
            << *itt->second.get() << "\n";
        // update each assumption proof node with the expanded proof node of
        // that assumption
        for (ProofNode* pfn : fap.second)
        {
          d_manager->updateNode(pfn, itt->second.get());
        }
      }
      // mark the fact as expanded
      expanded.insert(cur);
      Trace("lazy-cdproofchain-debug")
          << "LazyCDProofChain::getProofFor: expanded proof node: "
          << *it->second.get() << "\n";
    }
  } while (!visit.empty());
  if (!expanded.count(cur))
  {
    return nullptr;
  }
  // final proof of fact
  Assert(expandedToConnect.find(cur) != expandedToConnect.end());
  return expandedToConnect[cur];
}

void LazyCDProofChain::addLazyStep(Node expected,
                                   ProofGenerator* pg,
                                   bool isClosed,
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
  if (isClosed && options::proofNewEagerChecking())
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
