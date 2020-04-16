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

CDProof::CDProof(ProofNodeManager* pnm, context::Context* c)
    : d_manager(pnm), d_context(), d_nodes(c ? c : &d_context)
{
}

CDProof::~CDProof() {}

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
                           PfRule id,
                           const std::vector<Node>& children,
                           const std::vector<Node>& args,
                           bool ensureChildren,
                           bool forceOverwrite)
{
  // we must provide expected
  Assert(!expected.isNull());

  NodeProofNodeMap::iterator it = d_nodes.find(expected);
  if (it != d_nodes.end())
  {
    if (!forceOverwrite
        && ((*it).second->getId() != PfRule::ASSUME || id == PfRule::ASSUME))
    {
      // we do not overwrite if forceOverwrite is false and the previously
      // provided step was not an assumption, or if the currently provided step
      // is a (duplicate) assumption
      return expected;
    }
    // we will overwrite the existing proof node by updating its contents below
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
      pc = d_manager->mkNode(PfRule::ASSUME, pcassume, pcargs, c);
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
    // update its value
    pthis = (*it).second;
    d_manager->updateNode(pthis.get(), id, pchildren, args);
  }
  // the result of the proof node should be expected
  Assert(pthis->getResult() == expected);
  return expected;
}

Node CDProof::registerProof(Node expected,
                            std::shared_ptr<ProofNode> pn,
                            bool overwrite)
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
      const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& c : cs)
      {
        visit.push_back(c);
      }
    }
    else if (it->second.isNull())
    {
      itr = d_nodes.find(curFact);
      if (itr != d_nodes.end() && (*itr).second->getId() != PfRule::ASSUME)
      {
        // if we already have a proof for this fact, we keep it
        visited[cur] = curFact;
      }
      else
      {
        // if we don't, we must register the step
        std::vector<Node> pexp;
        const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
        for (const std::shared_ptr<ProofNode>& c : cs)
        {
          Assert(!c->getResult().isNull());
          pexp.push_back(c->getResult());
        }
        // can ensure children at this point
        Node res = registerStep(
            curFact, cur->getId(), pexp, cur->getArguments(), true, overwrite);
        Assert(!res.isNull());
        visited[cur] = res;
      }
    }
  } while (!visit.empty());

  return expected;
}

}  // namespace CVC4
