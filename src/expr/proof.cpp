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

CDProof::CDProof(context::Context* c, ProofChecker* pc)
    : d_checker(pc), d_nodes(c)
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

Node CDProof::registerStep(Node fact,
                           ProofStep id,
                           const std::vector<Node>& children,
                           const std::vector<Node>& args,
                           bool ensureChildren)
{
  NodeProofNodeMap::iterator it = d_nodes.find(fact);
  if (it != d_nodes.end())
  {
    if ((*it).second->getId() != ProofStep::ASSUME || id == ProofStep::ASSUME)
    {
      // already proven or assumed, nothing to do
      return fact;
    }
    // we will overwrite assumption
  }

  // collect the child proofs
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
      std::shared_ptr<ProofNode> pchild =
          std::make_shared<ProofNode>(ProofStep::ASSUME, pcassume, pcargs);
      d_nodes.insert(c, pchild);
      pchild->d_proven = c;
    }
    pchildren.push_back(pc);
  }

  // create or reinitialize it
  std::shared_ptr<ProofNode> pthis;
  if (it == d_nodes.end())
  {
    pthis = std::make_shared<ProofNode>(id, pchildren, args);
    d_nodes.insert(fact, pthis);
  }
  else
  {
    Assert(pthis->d_proven == fact);
    // overwrite its value
    pthis = (*it).second;
    pthis->setValue(id, pchildren, args);
  }
  if (d_checker)
  {
    // if we have a checker, check it
    d_checker->check(pthis.get(), fact);
  }
  else
  {
    // otherwise we trust it
    pthis->d_proven = fact;
  }
  return pthis->d_proven;
}

Node CDProof::registerProof(Node fact, std::shared_ptr<ProofNode> pn)
{
  if (pn->d_proven != fact)
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
    curFact = cur->d_proven;
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      itr = d_nodes.find(curFact);
      if (itr != d_nodes.end() && (*itr).second->getId() != ProofStep::ASSUME)
      {
      // if we already have a proof for this fact, we are done
        visited[cur] = curFact;
      }
      else
      {
        // otherwise, visit the children
        visited[cur] = Node::null();
        visit.push_back(cur);
        for (const std::shared_ptr<ProofNode>& c : cur->d_children)
        {
          visit.push_back(c);
        }
      }
    }
    else if (it->second.isNull())
    {
      // now, register the step
      std::vector<Node> pexp;
      for (const std::shared_ptr<ProofNode>& c : cur->d_children)
      {
        Assert(!c->d_proven.isNull());
        pexp.push_back(c->d_proven);
      }
      // can ensure children at this point
      Node res = registerStep(curFact, cur->d_id, pexp, cur->d_args, true);
      Assert(!res.isNull());
      visited[cur] = res;
    }
  } while (!visit.empty());

  return fact;
}

}  // namespace CVC4
