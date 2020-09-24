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

#include "expr/proof.h"
#include "expr/proof_node_algorithm.h"
#include "options/smt_options.h"

namespace CVC4 {

LazyCDProofChain::LazyCDProofChain(ProofNodeManager* pnm,
                                   bool cyclic,
                                   context::Context* c)
    : d_manager(pnm), d_cyclic(cyclic), d_context(), d_gens(c ? c : &d_context)
{
}

LazyCDProofChain::~LazyCDProofChain() {}

const std::map<Node, std::shared_ptr<ProofNode>> LazyCDProofChain::getLinks()
    const
{
  std::map<Node, std::shared_ptr<ProofNode>> links;
  for (const std::pair<const Node, ProofGenerator*>& link : d_gens)
  {
    Assert(link.second);
    std::shared_ptr<ProofNode> pfn = link.second->getProofFor(link.first);
    Assert(pfn);
    links[link.first] = pfn;
  }
  return links;
}

std::shared_ptr<ProofNode> LazyCDProofChain::getProofFor(Node fact)
{
  Trace("lazy-cdproofchain")
      << "LazyCDProofChain::getProofFor " << fact << "\n";
  // which facts have had proofs retrieved for. This is maintained to avoid
  // cycles. It also saves the proof node of the fact
  std::unordered_map<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      toConnect;
  // leaves of proof node links in the chain, i.e. assumptions, yet to be
  // expanded
  std::unordered_map<Node,
                     std::vector<std::shared_ptr<ProofNode>>,
                     NodeHashFunction>
      assumptionsToExpand;
  // invariant of the loop below, the first iteration notwhistanding:
  //   visit = domain(assumptionsToExpand) \ domain(toConnect)
  std::vector<Node> visit{fact};
  std::unordered_map<Node, bool, NodeHashFunction> visited;
  Node cur;
  do
  {
    cur = visit.back();
    visit.pop_back();
    auto itVisited = visited.find(cur);
    // pre-traversal
    if (itVisited == visited.end())
    {
      Trace("lazy-cdproofchain")
          << "LazyCDProofChain::getProofFor: check " << cur << "\n";
      ProofGenerator* pg = getGeneratorFor(cur);
      if (!pg)
      {
        Trace("lazy-cdproofchain")
            << "LazyCDProofChain::getProofFor: nothing to do\n";
        // nothing to do for this fact, it'll be a leaf in the final proof node,
        // don't post-traverse.
        visited[cur] = true;
        continue;
      }
      Trace("lazy-cdproofchain")
          << "LazyCDProofChain::getProofFor: Call generator " << pg->identify()
          << " for chain link " << cur << "\n";
      std::shared_ptr<ProofNode> curPfn = pg->getProofFor(cur);
      Trace("lazy-cdproofchain-debug")
          << "LazyCDProofChain::getProofFor: stored proof: " << *curPfn.get()
          << "\n";
      // retrieve free assumptions and their respective proof nodes
      std::map<Node, std::vector<std::shared_ptr<ProofNode>>> famap;
      expr::getFreeAssumptionsMap(curPfn, famap);
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
      // map node whose proof node must be expanded to the respective poof node
      toConnect[cur] = curPfn;
      // mark for post-traversal if we are controlling cycles
      if (d_cyclic)
      {
        visit.push_back(cur);
        visited[cur] = false;
        Trace("lazy-cdproofchain") << push;
        Trace("lazy-cdproofchain-debug") << push;
      }
      else
      {
        visited[cur] = true;
      }
      // enqueue free assumptions to process
      for (const std::pair<const Node, std::vector<std::shared_ptr<ProofNode>>>&
               fap : famap)
      {
        // check cycles, which are cases in which the assumption has already
        // been marked to be connected but we have not finished processing the
        // nodes it depends on
        if (d_cyclic && toConnect.find(fap.first) != toConnect.end()
            && std::find(visit.begin(), visit.end(), fap.first) != visit.end())
        {
          // Since we have a cycle with an assumption, this fact will be an
          // assumption in the final proof node produced by this method. This we
          // mark the proof node it results on, i.e. its value in the toConnect
          // map, as an assumption proof node. Note that we don't assign
          // visited[fap.first] to true so that we properly pop the traces
          // previously pushed.
          Trace("lazy-cdproofchain")
              << "LazyCDProofChain::getProofFor: removing cyclic assumption "
              << fap.first << " from expansion\n";
          toConnect[fap.first] = fap.second[0];
          continue;
        }
        // only process further the assumptions not already in the map
        auto it = assumptionsToExpand.find(fap.first);
        if (it == assumptionsToExpand.end())
        {
          visit.push_back(fap.first);
        }
        // add assumption proof nodes to be updated
        assumptionsToExpand[fap.first].insert(
            assumptionsToExpand[fap.first].end(),
            fap.second.begin(),
            fap.second.end());
      }
    }
    else if (!itVisited->second)
    {
      visited[cur] = true;
      Trace("lazy-cdproofchain") << pop;
      Trace("lazy-cdproofchain-debug") << pop;
    }
  } while (!visit.empty());
  // expand all assumptions marked to be connected
  for (const std::pair<const Node, std::shared_ptr<ProofNode>>& npfn :
       toConnect)
  {
    auto it = assumptionsToExpand.find(npfn.first);
    if (it == assumptionsToExpand.end())
    {
      Assert(npfn.first == fact);
      continue;
    }
    Trace("lazy-cdproofchain")
        << "LazyCDProofChain::getProofFor: expand assumption " << npfn.first
        << "\n";
    Trace("lazy-cdproofchain-debug")
        << "LazyCDProofChain::getProofFor: ...expand to " << *npfn.second.get()
        << "\n";
    // update each assumption proof node
    for (std::shared_ptr<ProofNode> pfn : it->second)
    {
      d_manager->updateNode(pfn.get(), npfn.second.get());
    }
  }
  // final proof of fact
  auto it = toConnect.find(fact);
  if (it == toConnect.end())
  {
    return nullptr;
  }
  return it->second;
}

void LazyCDProofChain::addLazyStep(Node expected, ProofGenerator* pg)
{
  Assert(pg != nullptr);
  Trace("lazy-cdproofchain") << "LazyCDProofChain::addLazyStep: " << expected
                             << " set to generator " << pg->identify() << "\n";
  // note this will replace the generator for expected, if any
  d_gens.insert(expected, pg);
}

void LazyCDProofChain::addLazyStep(Node expected,
                                   ProofGenerator* pg,
                                   const std::vector<Node>& assumptions,
                                   const char* ctx)
{
  Assert(pg != nullptr);
  Trace("lazy-cdproofchain") << "LazyCDProofChain::addLazyStep: " << expected
                             << " set to generator " << pg->identify() << "\n";
  // note this will rewrite the generator for expected, if any
  d_gens.insert(expected, pg);
  // check if chain is closed if options::proofNewEagerChecking() is on
  if (options::proofNewEagerChecking())
  {
    Trace("lazy-cdproofchain")
        << "LazyCDProofChain::addLazyStep: Checking closed proof...\n";
    std::shared_ptr<ProofNode> pfn = pg->getProofFor(expected);
    std::vector<Node> allowedLeaves{assumptions.begin(), assumptions.end()};
    // add all current links in the chain
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
  return d_gens.find(fact) != d_gens.end();
}

ProofGenerator* LazyCDProofChain::getGeneratorFor(Node fact)
{
  auto it = d_gens.find(fact);
  if (it != d_gens.end())
  {
    return (*it).second;
  }
  return nullptr;
}

std::string LazyCDProofChain::identify() const { return "LazyCDProofChain"; }

}  // namespace CVC4
