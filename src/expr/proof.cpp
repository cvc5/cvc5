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

std::shared_ptr<ProofNode> CDProof::mkProof(Node fact)
{
  std::shared_ptr<ProofNode> pf = getProofSymm(fact);
  if (pf != nullptr)
  {
    return pf;
  }
  // add as assumption
  std::vector<Node> pargs = {fact};
  std::vector<std::shared_ptr<ProofNode>> passume;
  std::shared_ptr<ProofNode> pfa =
      d_manager->mkNode(PfRule::ASSUME, passume, pargs, fact);
  d_nodes.insert(fact, pfa);
  return pfa;
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

std::shared_ptr<ProofNode> CDProof::getProofSymm(Node fact)
{
  Trace("cdproof") << "CDProof::getProofSymm: " << fact << std::endl;
  std::shared_ptr<ProofNode> pf = getProof(fact);
  if (pf != nullptr && !isAssumption(pf.get()))
  {
    Trace("cdproof") << "...existing non-assume " << pf->getRule() << std::endl;
    return pf;
  }
  if (fact.getKind() != EQUAL || fact[0] == fact[1])
  {
    Trace("cdproof") << "...no possible symm" << std::endl;
    // no symmetry possible, return original proof (possibly assumption)
    return pf;
  }
  // See if a proof exists for the opposite direction, if so, add the step.
  // Notice that SYMM is also disallowed.
  Node symFact = fact[1].eqNode(fact[0]);
  std::shared_ptr<ProofNode> pfs = getProof(symFact);
  if (pfs != nullptr)
  {
    // The symmetric fact exists, and the current one either does not, or is
    // an assumption. We make a new proof that applies SYMM to pfs.
    std::vector<std::shared_ptr<ProofNode>> pschild;
    pschild.push_back(pfs);
    std::vector<Node> args;
    if (pf == nullptr)
    {
      Trace("cdproof") << "...fresh make symm" << std::endl;
      std::shared_ptr<ProofNode> psym =
          d_manager->mkNode(PfRule::SYMM, pschild, args, fact);
      Assert(psym != nullptr);
      d_nodes.insert(fact, psym);
      return psym;
    }
    else if (!isAssumption(pfs.get()))
    {
      // if its not an assumption, make the connection
      Trace("cdproof") << "...update symm" << std::endl;
      // update pf
      bool sret = d_manager->updateNode(pf.get(), PfRule::SYMM, pschild, args);
      AlwaysAssert(sret);
    }
  }
  else
  {
    Trace("cdproof") << "...no symm, return "
                     << (pf == nullptr ? "null" : "non-null") << std::endl;
  }
  // return original proof (possibly assumption)
  return pf;
}

bool CDProof::addStep(Node expected,
                      PfRule id,
                      const std::vector<Node>& children,
                      const std::vector<Node>& args,
                      bool ensureChildren,
                      bool forceOverwrite)
{
  Trace("cdproof") << "CDProof::addStep: " << id << " " << expected
                   << ", ensureChildren = " << ensureChildren
                   << ", forceOverwrite = " << forceOverwrite << std::endl;
  if (id == PfRule::ASSUME || id == PfRule::SYMM)
  {
    // These rules are implicitly managed by this class. The user of this
    // class should not have to bother with them.
    // FIXME: return or assert here; this currently breaks slow-2020-04-17
  }
  // We must always provide expected to this method
  Assert(!expected.isNull());

  std::shared_ptr<ProofNode> pprev = getProofSymm(expected);
  if (pprev != nullptr)
  {
    if (!shouldOverwrite(pprev.get(), id, forceOverwrite))
    {
      // we should not overwrite the current step
      Trace("cdproof") << "...success, no overwrite" << std::endl;
      return true;
    }
    Trace("cdproof") << "existing proof " << pprev->getRule()
                     << ", overwrite..." << std::endl;
    // we will overwrite the existing proof node by updating its contents below
  }
  // collect the child proofs, for each premise
  std::vector<std::shared_ptr<ProofNode>> pchildren;
  for (const Node& c : children)
  {
    Trace("cdproof") << "- get child " << c << std::endl;
    std::shared_ptr<ProofNode> pc = getProofSymm(c);
    if (pc == nullptr)
    {
      if (ensureChildren)
      {
        // failed to get a proof for a child, fail
        Trace("cdproof") << "...fail, no child" << std::endl;
        return false;
      }
      Trace("cdproof") << "--- add assume" << std::endl;
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

  if (id == PfRule::SYMM)
  {
    Assert(pchildren.size() == 1);
    if (isAssumption(pchildren[0].get()))
    {
      // the step we are constructing is an assumption, no use
      return true;
    }
  }

  bool ret = true;
  // create or update it
  std::shared_ptr<ProofNode> pthis;
  if (pprev == nullptr)
  {
    Trace("cdproof") << "CDProof::addStep: new node..." << std::endl;
    pthis = d_manager->mkNode(id, pchildren, args, expected);
    if (pthis == nullptr)
    {
      // failed to construct the node, perhaps due to a proof checking failure
      Trace("cdproof") << "...fail, proof checking" << std::endl;
      return false;
    }
    d_nodes.insert(expected, pthis);
  }
  else
  {
    Trace("cdproof") << "CDProof::addStep: update node..." << std::endl;
    // update its value
    pthis = pprev;
    // We return the value of updateNode here. This means this method may return
    // false if this call failed, regardless of whether we already have a proof
    // step for expected.
    ret = d_manager->updateNode(pthis.get(), id, pchildren, args);
  }
  // the result of the proof node should be expected
  Assert(pthis->getResult() == expected);

  // ensure SYMM proof is also linked to an existing proof, if it is an
  // assumption.
  if (expected.getKind() == EQUAL && expected[0] != expected[1])
  {
    Node expectedSym = expected[1].eqNode(expected[0]);
    Trace("cdproof") << "CDProof::addStep: check update symmetry "
                     << expectedSym << std::endl;
    // if it exists, we may need to update it
    std::shared_ptr<ProofNode> pfs = getProof(expectedSym);
    if (pfs != nullptr)
    {
      // call the get function with symmetry
      std::shared_ptr<ProofNode> pfss = getProofSymm(expectedSym);
    }
  }
  Trace("cdproof") << "...return " << ret << std::endl;
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

bool CDProof::addProof(std::shared_ptr<ProofNode> pn,
                       bool forceOverwrite,
                       bool doCopy)
{
  if (!doCopy)
  {
    // If we aren't doing a deep copy, we either store pn or link its top
    // node into the existing pointer
    Node curFact = pn->getResult();
    std::shared_ptr<ProofNode> cur = getProofSymm(curFact);
    if (cur == nullptr)
    {
      // Assert that the checker of this class agrees with (the externally
      // provided) pn. This ensures that if pn was checked by a different
      // checker than the one of the manager in this class, then it is double
      // checked here, so that this class maintains the invariant that all of
      // its nodes in d_nodes have been checked by the underlying checker.
      Assert(d_manager->getChecker() == nullptr
             || d_manager->getChecker()->check(pn.get(), curFact) == curFact);
      // just store the proof for fact
      d_nodes.insert(curFact, pn);
    }
    else if (shouldOverwrite(cur.get(), pn->getRule(), forceOverwrite))
    {
      // We update cur to have the structure of the top node of pn. Notice that
      // the interface to update this node will ensure that the proof apf is a
      // proof of the assumption. If it does not, then pn was wrong.
      if (!d_manager->updateNode(
              cur.get(), pn->getRule(), pn->getChildren(), pn->getArguments()))
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
  visit.push_back(pn.get());
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

bool CDProof::hasStep(Node fact)
{
  std::shared_ptr<ProofNode> pf = getProofSymm(fact);
  if (pf != nullptr && !isAssumption(pf.get()))
  {
    return true;
  }
  return false;
}

ProofNodeManager* CDProof::getManager() const { return d_manager; }

bool CDProof::shouldOverwrite(ProofNode* pn, PfRule newId, bool forceOverwrite)
{
  Assert(pn != nullptr);
  // we overwrite only if forceOverwrite is true, or if the previously
  // provided proof pn was an assumption and the currently provided step is not
  return forceOverwrite || (isAssumption(pn) && newId != PfRule::ASSUME);
}

bool CDProof::isAssumption(ProofNode* pn)
{
  PfRule rule = pn->getRule();
  if (rule == PfRule::ASSUME)
  {
    return true;
  }
  else if (rule == PfRule::SYMM)
  {
    const std::vector<std::shared_ptr<ProofNode>>& pc = pn->getChildren();
    Assert(pc.size() == 1);
    return pc[0]->getRule() == PfRule::ASSUME;
  }
  return false;
}

}  // namespace CVC4
