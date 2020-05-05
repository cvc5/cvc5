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

bool CDProof::addStep(Node expected,
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
    if (!shouldOverwrite((*it).second.get(),id,forceOverwrite))
    {
      // we should not overwrite the current step
      return true;
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
        return false;
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

  bool ret = true;
  // create or update it
  std::shared_ptr<ProofNode> pthis;
  if (it == d_nodes.end())
  {
    pthis = d_manager->mkNode(id, pchildren, args, expected);
    if (pthis == nullptr)
    {
      // failed to construct the node, perhaps due to a proof checking failure
      return false;
    }
    d_nodes.insert(expected, pthis);
  }
  else
  {
    // update its value
    pthis = (*it).second;
    // We return the value of updateNode here. This means this method may return
    // false if this call failed, regardless of whether we already have a proof
    // step for expected.
    ret = d_manager->updateNode(pthis.get(), id, pchildren, args);
  }
  // the result of the proof node should be expected
  Assert(pthis->getResult() == expected);
  return ret;
}

bool CDProof::addStep(Node expected,
                      const ProofStep& step,
                      bool ensureChildren,
                      bool forceOverwrite)
{
  return addStep(expected, step.d_rule, step.d_children, step.d_args);
}

bool CDProof::addSteps(const ProofStepBuffer& psb,
              bool ensureChildren,
              bool forceOverwrite)
{
  const std::vector<std::pair<Node, ProofStep>>& steps = psb.getSteps();
  for (const std::pair<Node, ProofStep>& ps : steps)
  {
    if (!addStep(ps.first, ps.second, ensureChildren, forceOverwrite))
    {
      return false;
    }
  }
  return true;
}

bool CDProof::addProof(std::shared_ptr<ProofNode> pn, bool forceOverwrite, bool doCopy)
{
  if (!doCopy)
  {
    // If we aren't doing a deep copy, we either store pn or link its top
    // node into the existing pointer
    Node curFact = pn->getResult();
    std::shared_ptr<ProofNode> cur = getProof(curFact);
    if (cur==nullptr)
    {
      // Assert that the checker of this class agrees with (the externally
      // provided) pn. This ensures that if pn was checked by a different
      // checker than the one of the manager in this class, then it is double
      // checked here, so that this class maintains the invariant that all of
      // its nodes in d_nodes have been checked by the underlying checker.
      Assert (d_manager->getChecker()==nullptr || 
      d_manager->getChecker()->check(pn,curFact)==curFact);
      // just store the proof for fact
      d_nodes.insert(curFact,pn);
    }
    else if (shouldOverwrite(cur.get(),pn->getRule(),forceOverwrite))
    {
      // We update cur to have the structure of the top node of pn. Notice that
      // the interface to update this node will ensure that the proof apf is a
      // proof of the assumption. If it does not, then pn was wrong.
      if (!d_manager->updateNode(cur.get(),
                                  pn->getRule(),
                                  pn->getChildren(),
                                  pn->getArguments()))
      {
        return false;
      }
    }
    return true;
  }
  std::unordered_map<ProofNode*, bool> visited;
  std::unordered_map<ProofNode*, bool>::iterator it;
  std::vector<ProofNode*> visit;
  ProofNode* cur;
  Node curFact;
  visit.push_back(pn);
  bool retValue = true;
  do
  {
    cur = visit.back();
    curFact = cur->getResult();
    visit.pop_back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      // visit the children
      visited[cur] = false;
      visit.push_back(cur);
      const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& c : cs)
      {
        visit.push_back(c.get());
      }
    }
    else if (!it->second)
    {
      // we always call addStep, which may or may not overwrite the
      // current step
      std::vector<Node> pexp;
      const std::vector<std::shared_ptr<ProofNode>>& cs = cur->getChildren();
      for (const std::shared_ptr<ProofNode>& c : cs)
      {
        Assert(!c->getResult().isNull());
        pexp.push_back(c->getResult());
      }
      // can ensure children at this point
      bool res = addStep(curFact,
                         cur->getRule(),
                         pexp,
                         cur->getArguments(),
                         true,
                         forceOverwrite);
      // should always succeed
      Assert(res);
      retValue = retValue && res;
      visited[cur] = true;
    }
  } while (!visit.empty());

  return retValue;
}

bool CDProof::hasStep(Node fact) const
{
  NodeProofNodeMap::iterator it = d_nodes.find(fact);
  if (it == d_nodes.end())
  {
    return false;
  }
  // cannot be an ASSUME
  return true && (*it).second->getRule() != PfRule::ASSUME;
}

ProofNodeManager* CDProof::getManager() const { return d_manager; }

bool CDProof::shouldOverwrite(ProofNode * pn, PfRule newId, bool forceOverwrite)
{
  Assert (pn!=nullptr);
  // we overwrite only if forceOverwrite is true, or if the previously
  // provided proof pn was an assumption and the currently provided step is not
  return forceOverwrite || (pn->getRule() == PfRule::ASSUME && newId != PfRule::ASSUME);
}

}  // namespace CVC4
