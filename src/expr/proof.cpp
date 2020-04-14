/*********************                                                        */
/*! \file proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of proof
 **/

#include "expr/proof.h"

using namespace CVC4::kind;

namespace CVC4 {

CDProof::CDProof(context::Context* c, ProofNodeManager* pnm)
    : d_manager(pnm), d_nodes(c)
{
}

std::shared_ptr<ProofNode> CDProof::getProof(Node fact) const
{
  NodeProofNodeMap::iterator it = d_nodes.find(fact);
  if (it != d_nodes.end())
  {
    return (*it).second;
  }
  return nullptr;
}

Node CDProof::registerStep(Node expected,
                           ProofStep id,
                           const std::vector<Node>& children,
                           const std::vector<Node>& args,
                           bool ensureChildren)
{
  NodeProofNodeMap::iterator it = d_nodes.find(expected);
  if (it != d_nodes.end())
  {
    if ((*it).second->getId() != ProofStep::ASSUME || id == ProofStep::ASSUME)
    {
      // already proven or duplicate assumption, nothing to do
      return expected;
    }
    // we will overwrite assumption
  }

  // collect the child proofs, for each premise
  std::vector<std::shared_ptr<ProofNode>> pchildren;
  for (const Node& c : children)
  {
    std::shared_ptr<ProofNode> pc = getProof(c);
    if (pc == nullptr)
    {
      if (ensureChildren)
      {
        // failed to get a proof for a child, fail
        return Node::null();
      }
      // otherwise, we initialize it as an assumption
      std::vector<Node> pcargs = {c};
      std::vector<std::shared_ptr<ProofNode>> pcassume;
      pc = d_manager->mkNode(ProofStep::ASSUME, pcassume, pcargs, c);
      // assumptions never fail to check
      Assert(pc != nullptr);
      d_nodes.insert(c, pc);
    }
    pchildren.push_back(pc);
  }

  // create or reinitialize it
  std::shared_ptr<ProofNode> pthis;
  if (it == d_nodes.end())
  {
    pthis = d_manager->mkNode(id, pchildren, args, expected);
    if (pthis == nullptr)
    {
      // failed to construct the node, perhaps due to a proof checking failure
      return Node::null();
    }
    d_nodes.insert(expected, pthis);
  }
  else
  {
    // overwrite its value
    pthis = (*it).second;
    d_manager->updateNode(pthis.get(), id, pchildren, args);
  }
  return pthis->getResult();
}

Node CDProof::registerProof(Node expected, std::shared_ptr<ProofNode> pn)
{
  if (pn->getResult() != expected)
  {
    // something went wrong
    return Node::null();
  }
  std::unordered_map<std::shared_ptr<ProofNode>, Node> visited;
  std::unordered_map<std::shared_ptr<ProofNode>, Node>::iterator it;
  std::vector<std::shared_ptr<ProofNode>> visit;
  NodeProofNodeMap::iterator itr;
  std::shared_ptr<ProofNode> cur;
  Node curFact;
  visit.push_back(pn);
  do
  {
    cur = visit.back();
    curFact = cur->getResult();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      // visit the children
      visited[cur] = Node::null();
      visit.push_back(cur);
      for (const std::shared_ptr<ProofNode>& c : cur->d_children)
      {
        visit.push_back(c);
      }
    }
    else if (it->second.isNull())
    {
      itr = d_nodes.find(curFact);
      if (itr != d_nodes.end() && (*itr).second->getId() != ProofStep::ASSUME)
      {
        // if we already have a proof for this fact, we keep it
        visited[cur] = curFact;
      }
      else
      {
        // if we don't, we must register the step
        std::vector<Node> pexp;
        for (const std::shared_ptr<ProofNode>& c : cur->d_children)
        {
          Assert(!c->getResult().isNull());
          pexp.push_back(c->d_proven);
        }
        // can ensure children at this point
        Node res = registerStep(
            curFact, cur->getId(), pexp, cur->getArguments(), true);
        Assert(!res.isNull());
        visited[cur] = res;
      }
    }
  } while (!visit.empty());

  return expected;
}

}  // namespace CVC4
