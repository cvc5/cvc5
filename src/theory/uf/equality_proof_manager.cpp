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
    : d_ee(ee), d_checker(pc), d_proof(c, pc)
{
}

std::shared_ptr<ProofNode> EqProofManager::getProof(Node fact) const
{
  return d_proof.getProof(fact);
}

Node EqProofManager::pfRefl(Node a)
{
  Node fact = a.eqNode(a);
  std::vector<Node> children;
  std::vector<Node> args;
  args.push_back(a);
  return d_proof.registerStep(fact, ProofStep::REFL, children, args);
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
  return d_proof.registerStep(fact, ProofStep::REWRITE, children, args);
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
  return d_proof.registerStep(fact, ProofStep::SUBS, exp, args, ensureChildren);
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
  return d_proof.registerStep(
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
  return d_proof.registerStep(eqSymm, ProofStep::SYMM, children, args, ensureChildren);
}

}  // namespace eq
}  // namespace theory
}  // namespace CVC4
