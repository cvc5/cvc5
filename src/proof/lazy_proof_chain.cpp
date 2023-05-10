/******************************************************************************
 * Top contributors (to current version):
 *   Haniel Barbosa, Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of lazy proof utility.
 */

#include "proof/lazy_proof_chain.h"

#include "options/proof_options.h"
#include "proof/proof.h"
#include "proof/proof_ensure_closed.h"
#include "proof/proof_node.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"

namespace cvc5::internal {

LazyCDProofChain::LazyCDProofChain(Env& env,
                                   bool cyclic,
                                   context::Context* c,
                                   ProofGenerator* defGen,
                                   bool defRec,
                                   const std::string& name)
    : CDProof(env, c, name, false),
      d_cyclic(cyclic),
      d_defRec(defRec),
      d_context(),
      d_gens(c ? c : &d_context),
      d_defGen(defGen),
      d_name(name)
{
}

LazyCDProofChain::~LazyCDProofChain() {}

const std::map<Node, std::shared_ptr<ProofNode>> LazyCDProofChain::getLinks()
    const
{
  std::map<Node, std::shared_ptr<ProofNode>> links;
  for (const std::pair<const Node, ProofGenerator* const>& link : d_gens)
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
      << "LazyCDProofChain::getProofFor of gen " << d_name << "\n";
  Trace("lazy-cdproofchain")
      << "LazyCDProofChain::getProofFor: " << fact << "\n";
  // which facts have had proofs retrieved for. This is maintained to avoid
  // cycles. It also saves the proof node of the fact
  std::unordered_map<Node, std::shared_ptr<ProofNode>> toConnect;
  // leaves of proof node links in the chain, i.e. assumptions, yet to be
  // expanded
  std::unordered_map<Node, std::vector<std::shared_ptr<ProofNode>>>
      assumptionsToExpand;
  // invariant of the loop below, the first iteration notwithstanding:
  //   visit = domain(assumptionsToExpand) \ domain(toConnect)
  std::vector<Node> visit{fact};
  std::unordered_map<Node, bool> visited;
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
      Assert(toConnect.find(cur) == toConnect.end());
      // The current fact may be justified by concrete steps added to this
      // proof, in which case we do not use the generators.
      bool rec = true;
      std::shared_ptr<ProofNode> curPfn = getProofForInternal(cur, rec);
      if (curPfn == nullptr)
      {
        Trace("lazy-cdproofchain")
            << "LazyCDProofChain::getProofFor: No proof found, skip\n";
        visited[cur] = true;
        continue;
      }
      // map node whose proof node must be expanded to the respective poof
      // node
      toConnect[cur] = curPfn;
      // We may not want to recursively connect this proof so we skip.
      if (!rec)
      {
        visited[cur] = true;
        continue;
      }
      Trace("lazy-cdproofchain-debug")
          << "LazyCDProofChain::getProofFor: stored proof: " << *curPfn.get()
          << "\n";
      // retrieve free assumptions and their respective proof nodes
      std::map<Node, std::vector<std::shared_ptr<ProofNode>>> famap;
      expr::getFreeAssumptionsMap(curPfn, famap);
      if (d_cyclic)
      {
        // First check for a trivial cycle, which is when cur is a free
        // assumption of curPfn. Note that in the special case in the special
        // case in which curPfn has cur as an assumption and cur is actually the
        // initial fact that getProofFor is called on, the general cycle
        // detection below would prevent this method from generating a proof for
        // cur, which would be wrong since there is a justification for it in
        // curPfn.
        bool isCyclic = false;
        for (const auto& fap : famap)
        {
          if (cur == fap.first)
          {
            // connect it to one of the assumption proof nodes
            toConnect[cur] = fap.second[0];
            isCyclic = true;
            break;
          }
        }
        if (isCyclic)
        {
          Trace("lazy-cdproofchain")
              << "LazyCDProofChain::getProofFor: trivial cycle detected for "
              << cur << ", abort\n";
          visited[cur] = true;
          continue;
        }
        if (TraceIsOn("lazy-cdproofchain"))
        {
          unsigned alreadyToVisit = 0;
          Trace("lazy-cdproofchain")
              << "LazyCDProofChain::getProofFor: " << famap.size()
              << " free assumptions:\n";
          for (auto fap : famap)
          {
            Trace("lazy-cdproofchain")
                << "LazyCDProofChain::getProofFor:  - " << fap.first << "\n";
            alreadyToVisit +=
                std::find(visit.begin(), visit.end(), fap.first) != visit.end()
                    ? 1
                    : 0;
          }
          Trace("lazy-cdproofchain")
              << "LazyCDProofChain::getProofFor: " << alreadyToVisit
              << " already to visit\n";
        }
        // If we are controlling cycle, check whether any of the assumptions of
        // cur would provoke a cycle. In such we remove cur from toConnect and
        // do not proceed to expand any of its assumptions.
        Trace("lazy-cdproofchain") << "LazyCDProofChain::getProofFor: marking "
                                   << cur << " for cycle check\n";
        // enqueue free assumptions to process
        for (const auto& fap : famap)
        {
          // A cycle is characterized by cur having an assumption being
          // *currently* expanded that is seen again, i.e. in toConnect and not
          // yet post-visited
          auto itToConnect = toConnect.find(fap.first);
          if (itToConnect != toConnect.end() && !visited[fap.first])
          {
            // Since we have a cycle with an assumption, cur will be an
            // assumption in the final proof node produced by this
            // method.
            Trace("lazy-cdproofchain")
                << "LazyCDProofChain::getProofFor: cyclic assumption "
                << fap.first << "\n";
            isCyclic = true;
            break;
          }
        }
        if (isCyclic)
        {
          visited[cur] = true;
          Trace("lazy-cdproofchain")
              << "LazyCDProofChain::getProofFor: Removing " << cur
              << " from toConnect\n";
          auto itToConnect = toConnect.find(cur);
          toConnect.erase(itToConnect);
          continue;
        }
        visit.push_back(cur);
        visited[cur] = false;
      }
      else
      {
        visited[cur] = true;
      }
      // enqueue free assumptions to process
      for (const auto& fap : famap)
      {
        Trace("lazy-cdproofchain")
            << "LazyCDProofChain::getProofFor: marking " << fap.first
            << " for revisit and for expansion (curr: "
            << assumptionsToExpand[fap.first].size()
            << ", adding: " << fap.second.size() << ")\n";
        // We always add assumptions to visit so that their last seen occurrence
        // is expanded (rather than the first seen occurrence, if we were not
        // adding assumptions, say, in assumptionsToExpand). This is so because
        // in the case where we are checking cycles this is necessary (and
        // harmless when we are not). For example the cycle
        //
        //                 a2
        //                ...
        //               ----
        //                a1
        //               ...
        //             --------
        //   a0   a1    a2
        //       ...
        //  ---------------
        //       n
        //
        // in which a2 has a1 as an assumption, which has a2 an assumption,
        // would not be captured if we did not revisit a1, which is an
        // assumption of n and this already occur in assumptionsToExpand when
        // it shows up again as an assumption of a2.
        visit.push_back(fap.first);
        // add assumption proof nodes to be updated
        assumptionsToExpand[fap.first].insert(
            assumptionsToExpand[fap.first].end(),
            fap.second.begin(),
            fap.second.end());
      }
      if (d_cyclic)
      {
        Trace("lazy-cdproofchain") << push;
        Trace("lazy-cdproofchain-debug") << push;
      }
    }
    else if (!itVisited->second)
    {
      visited[cur] = true;
      Trace("lazy-cdproofchain") << pop;
      Trace("lazy-cdproofchain-debug") << pop;
      Trace("lazy-cdproofchain")
          << "LazyCDProofChain::getProofFor: post-visited " << cur << "\n";
    }
    else
    {
      Trace("lazy-cdproofchain")
          << "LazyCDProofChain::getProofFor: already fully processed " << cur
          << "\n";
    }
  } while (!visit.empty());
  ProofNodeManager* pnm = getManager();
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
    Assert(npfn.second);
    Trace("lazy-cdproofchain")
        << "LazyCDProofChain::getProofFor: expand assumption " << npfn.first
        << "\n";
    Trace("lazy-cdproofchain-debug")
        << "LazyCDProofChain::getProofFor: ...expand to " << *npfn.second.get()
        << "\n";
    // update each assumption proof node
    for (std::shared_ptr<ProofNode> pfn : it->second)
    {
      pnm->updateNode(pfn.get(), npfn.second.get());
    }
  }
  Trace("lazy-cdproofchain") << "===========\n";
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
  // check if chain is closed if eager checking is on
  if (options().proof.proofCheck == options::ProofCheckMode::EAGER)
  {
    Trace("lazy-cdproofchain")
        << "LazyCDProofChain::addLazyStep: Checking closed proof...\n";
    std::shared_ptr<ProofNode> pfn = pg->getProofFor(expected);
    std::vector<Node> allowedLeaves{assumptions.begin(), assumptions.end()};
    // add all current links in the chain
    for (const std::pair<const Node, ProofGenerator* const>& link : d_gens)
    {
      allowedLeaves.push_back(link.first);
    }
    if (TraceIsOn("lazy-cdproofchain"))
    {
      Trace("lazy-cdproofchain") << "Checking relative to leaves...\n";
      for (const Node& n : allowedLeaves)
      {
        Trace("lazy-cdproofchain") << "  - " << n << "\n";
      }
      Trace("lazy-cdproofchain") << "\n";
    }
    pfnEnsureClosedWrt(
        options(), pfn.get(), allowedLeaves, "lazy-cdproofchain", ctx);
  }
}

bool LazyCDProofChain::hasGenerator(Node fact) const
{
  return d_gens.find(fact) != d_gens.end();
}

ProofGenerator* LazyCDProofChain::getGeneratorFor(Node fact)
{
  bool rec = true;
  return getGeneratorForInternal(fact, rec);
}

ProofGenerator* LazyCDProofChain::getGeneratorForInternal(Node fact, bool& rec)
{
  auto it = d_gens.find(fact);
  if (it != d_gens.end())
  {
    return (*it).second;
  }
  // otherwise, if no explicit generators, we use the default one
  if (d_defGen != nullptr)
  {
    rec = d_defRec;
    return d_defGen;
  }
  return nullptr;
}

std::shared_ptr<ProofNode> LazyCDProofChain::getProofForInternal(Node fact,
                                                                 bool& rec)
{
  std::shared_ptr<ProofNode> pfn = CDProof::getProofFor(fact);
  Assert(pfn != nullptr);
  // If concrete proof, save it, otherwise try generators.
  if (pfn->getRule() != PfRule::ASSUME)
  {
    return pfn;
  }
  ProofGenerator* pg = getGeneratorForInternal(fact, rec);
  if (!pg)
  {
    return nullptr;
  }
  Trace("lazy-cdproofchain")
      << "LazyCDProofChain::getProofFor: Call generator " << pg->identify()
      << " for chain link " << fact << "\n";
  return pg->getProofFor(fact);
}

std::string LazyCDProofChain::identify() const { return d_name; }

}  // namespace cvc5::internal
