/*********************                                                        */
/*! \file equality_proof_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of equality proof manager
 **/

#include "theory/uf/equality_proof_manager.h"

#include "theory/rewriter.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace eq {

EqProofManager::EqProofManager(context::Context* c,
                               EqualityEngine& ee,
                               ProofChecker* pc)
    : d_ee(ee), d_checker(pc), d_nodes(c)
{
}

Node EqProofManager::registerStep(Node fact,
                                  ProofStep id,
                                  const std::vector<Node>& children,
                                  const std::vector<Node>& args,
                                  bool ensureChildren)
{
  NodeProofMap::iterator it = d_nodes.find(fact);
  if (it == d_nodes.end())
  {
    if ((*it).second->getId() != ProofStep::ASSUME || id == ProofStep::ASSUME)
    {
      // already proven
      return fact;
    }
  }
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
    pthis = (*it).second;
    pthis->initialize(id, pchildren, args);
  }
  Node pfact = pthis->getResult();
  // must be equal to given fact
  if (fact == pfact)
  {
    // valid in this context
    return fact;
  }
  pthis->invalidate();
  return Node::null();
}

std::shared_ptr<ProofNode> EqProofManager::getProof(Node fact) const
{
  NodeProofMap::const_iterator it = d_nodes.find(fact);
  if (it == d_nodes.end())
  {
    // does not exist
    return nullptr;
  }
  return (*it).second;
}

Node EqProofManager::pfRefl(Node a)
{
  Node fact = a.eqNode(a);
  std::vector<Node> children;
  std::vector<Node> args;
  args.push_back(a);
  return registerStep(fact, ProofStep::REFL, children, args);
}

Node EqProofManager::pfRewrite(Node a)
{
  Node ar = Rewriter::rewrite(a);
  if (ar == a)
  {
    // no effect
    return pfRefl(a);
  }
  Node fact = a.eqNode(ar);
  std::vector<Node> children;
  std::vector<Node> args;
  args.push_back(a);
  return registerStep(fact, ProofStep::REWRITE, children, args);
}

Node pfRewriteFalse(Node eq, bool ensureChildren) { return Node::null(); }

Node EqProofManager::pfSubs(Node a,
                            const std::vector<Node>& exp,
                            bool ensureChildren)
{
  Node as = ProofNode::applySubstitution(a, exp);
  if (a == as)
  {
    // no effect
    return pfRefl(a);
  }
  Node fact = a.eqNode(as);
  std::vector<Node> args;
  args.push_back(a);
  return registerStep(fact, ProofStep::SUBS, exp, args, ensureChildren);
}

Node EqProofManager::pfSubsRewrite(Node a,
                                   const std::vector<Node>& exp,
                                   bool ensureChildren)
{
  Node eqSubs = pfSubs(a, exp, ensureChildren);
  Node eqRew = pfRewrite(eqSubs[0]);
  return pfTrans(eqSubs, eqRew, ensureChildren);
}

Node EqProofManager::pfEqualBySubsRewrite(Node a,
                                          Node b,
                                          const std::vector<Node>& exp,
                                          bool ensureChildren)
{
  Node eqA = pfSubsRewrite(a, exp, ensureChildren);
  Node eqB = pfSubsRewrite(b, exp, ensureChildren);
  Node eqBSymm = pfSymm(eqB, ensureChildren);
  return pfTrans(eqA, eqBSymm, ensureChildren);
}

Node EqProofManager::pfTrans(Node eq1, Node eq2, bool ensureChildren)
{
  Assert(eq1.getKind() == EQUAL);
  Assert(eq2.getKind() == EQUAL);
  if (eq1[1] != eq2[0])
  {
    // failed to connect
    return Node::null();
  }
  if (eq1[0] == eq1[1])
  {
    // one part is trivial
    return eq2;
  }
  else if (eq2[0] == eq2[1])
  {
    // other part is trivial
    return eq1;
  }
  // otherwise, we need to make the transitivity proof
  Node eqTrans = eq1[0].eqNode(eq2[1]);
  std::vector<Node> children;
  children.push_back(eq1);
  children.push_back(eq2);
  std::vector<Node> args;
  return registerStep(
      eqTrans, ProofStep::TRANS, children, args, ensureChildren);
}

Node EqProofManager::pfSymm(Node eq, bool ensureChildren)
{
  Assert(eq.getKind() == EQUAL);
  if (eq[0] == eq[1])
  {
    // not necessary
    return eq;
  }
  Node eqSymm = eq[1].eqNode(eq[0]);
  std::vector<Node> children;
  children.push_back(eq);
  std::vector<Node> args;
  return registerStep(eqSymm, ProofStep::SYMM, children, args, ensureChildren);
}

}  // namespace eq
}  // namespace theory
}  // namespace CVC4
