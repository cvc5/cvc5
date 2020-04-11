/*********************                                                        */
/*! \file strings_proof.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of strings proof manager
 **/

#include "theory/strings/proof_manager.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace strings {


Node ProofManager::registerStep(Node fact,
                                ProofStep id,
                                const std::vector<Node>& children,
                                const std::vector<Node>& args,
                                bool ensureChildren
                               )
{
  std::map<Node, std::unique_ptr<ProofNode> >::iterator it = d_nodes.find(fact);
  if (it != d_nodes.end() && it->second->getId()!=ProofStep::ASSUME)
  {
    // already proven
    return fact;
  }
  std::vector<ProofNode*> pchildren;
  for (const Node& c : children)
  {
    ProofNode* pc = getProof(c);
    if (pc == nullptr)
    {
      // failed to get a proof for child, fail
      if (ensureChildren)
      {
        return Node::null();
      }
      // otherwise, we initialize it as an assumption
      std::vector<Node> pcargs = { c };
      std::vector<ProofNode*> pcassume;
      d_nodes[c].reset(new ProofNode(ProofStep::ASSUME, pcassume, pcargs));
    }
    pchildren.push_back(pc);
  }
  // create or reinitialize it
  if (it==d_nodes.end())
  {
    d_nodes[fact].reset(new ProofNode(id, pchildren, args));
  }
  else
  {
    d_nodes[fact]->initialize(id, pchildren,args);
  }
  Node pfact = d_nodes[fact]->getResult();
  // must be equal to given fact
  if (fact == pfact)
  {
    return fact;
  }
  return Node::null();
}

ProofNode* ProofManager::getProof(Node fact) const
{
  std::map<Node, std::unique_ptr<ProofNode> >::const_iterator it =
      d_nodes.find(fact);
  if (it == d_nodes.end())
  {
    return nullptr;
  }
  return it->second.get();
}

Node ProofManager::pfRew(Node a)
{
  Node ar = Rewriter::rewrite(a);
  Node fact = a.eqNode(ar);
  ProofStep id = a==ar ? ProofStep::REFL : ProofStep::REWRITE;
  std::vector<Node> children;
  std::vector<Node> args;
  args.push_back(a);
  return registerStep(fact, id, children, args);
}

Node ProofManager::pfSubs(Node a, const std::vector<Node>& exp, bool ensureChildren)
{
  Node asubs = ProofNode::applySubstitution(a, exp);
  Node fact = a.eqNode(asubs);
  if (a==asubs)
  {
    id = ProofStep::
  }
}

Node ProofManager::pfSubsRew(Node a, const std::vector<Node>& exp, bool ensureChildren)
{
  Node eqSubs = pfSubs(a, exp, ensureChildren);
  Node eqRew = pfRew(eqSubs[0]);
  return pfTrans(eqSubs, eqRew, ensureChildren);
}

Node ProofManager::pfTrans(Node eq1, Node eq2, bool ensureChildren)
{
  Assert( eq1.getKind()==EQUAL);
  Assert( eq2.getKind()==EQUAL);
  if( eq1[1]!=eq2[0] )
  {
    return Node::null();
  }
  if (eq1[0]==eq1[1])
  {
    return eq2;
  }
  else if (eq2[0]==eq2[1])
  {
    return eq2;
  }
  Node eqTrans = eq1[0].eqNode(eq2[1]);
  std::vector<Node> children;
  children.push_back(eq1);
  children.push_back(eq2);
  std::vector<Node> args;
  return registerStep(eqTrans, ProofStep::TRANS, children, args, ensureChildren);
}

Node ProofManager::pfSymm(Node eq, bool ensureChildren)
{
  Assert(eq.getKind()==EQUAL);
  if (eq[0]==eq[1])
  {
    return eq;
  }
  Node eqSymm = eq[1].eqNode(eq[0]);
  std::vector<Node> children;
  children.push_back(eq);
  std::vector<Node> args;
  return registerStep(eqSymm, ProofStep::SYMM, children, args, ensureChildren);
}

Node ProofManager::pfEqualBySubsRew(Node a, Node b, const std::vector<Node>& exp,
                  bool ensureChildren)
{
  Node eqA = pfSubsRew(a, exp, ensureChildren);
  Node eqB = pfSubsRew(b, exp, ensureChildren);
  Node eqBSymm = pfSymm(eqB, ensureChildren);
  return pfTrans(eqA, eqBSymm, ensureChildren);
}
  
  
}  // namespace strings
}  // namespace theory
}  // namespace CVC4
