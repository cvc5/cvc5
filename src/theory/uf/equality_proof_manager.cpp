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
#include "theory/uf/equality_proof_checker.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace eq {

EqProofManager::EqProofManager(context::Context* c,
                               EqualityEngine& ee,
                               ProofChecker* pc)
    : d_ee(ee), d_checker(pc), d_proof(c, pc), d_proofsEnabled(true)
{
  d_true = NodeManager::currentNM()->mkConst(true);
}

Node EqProofManager::assert(Node lit, ProofStep id, const std::vector<Node>& exp)
{
  // first, justify its proof
  std::vector<Node> args;
  Node ret = d_proof.registerStep(lit, id, exp, args);

  // second, assert it to the equality engine
  Node reason = mkAnd(exp);
  assertInternal(lit, polarity, reason);
  return ret;
}

Node EqProofManager::assertEqualityAssume(Node lit)
{
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // first, justify its proof
  Node ret = pfAssume(lit);

  // second, assert it to the equality engine
  // it is its own explanation
  assertInternal(atom, polarity, lit);
  return ret;
}

Node EqProofManager::assertEqualitySubsRewrite(Node lit,
                                               const std::vector<Node>& exp)
{
  Node eq = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;
  Assert(eq.getKind() == EQUAL);

  // first, justify its proof
  Node ret;
  if (polarity)
  {
    // eq[0] = rewrite(eq[0].substitute(exp)) = rewrite(eq[1].substitute(exp)) =
    // eq[1]
    ret = pfEqualBySubsRewrite(eq[0], eq[1], exp);
  }
  else
  {
    // eq[0] = rewrite(eq[0].substitute(exp)) != rewrite(eq[1].substitute(exp))
    // = eq[1]
    ret = pfDisequalBySubsRewrite(eq[0], eq[1], exp);
  }

  // second, assert it to the equality engine
  Node reason = mkAnd(exp);
  assertInternal(eq, polarity, reason);
  return ret;
}

void EqProofManager::assertInternal(Node atom, bool polarity, TNode reason)
{
  if (atom.getKind() == EQUAL)
  {
    d_ee.assertEquality(atom, polarity, reason);
  }
  else
  {
    d_ee.assertPredicate(atom, polarity, reason);
  }
}

void EqProofManager::explain(Node lit, std::vector<TNode>& assertions)
{
  std::shared_ptr<eq::EqProof> pf =
      d_proofsEnabled ? std::make_shared<eq::EqProof>() : nullptr;
  bool polarity = lit.getKind() != NOT;
  TNode atom = polarity ? lit : lit[0];
  std::vector<TNode> tassumptions;
  if (atom.getKind() == EQUAL)
  {
    if (atom[0] != atom[1])
    {
      Assert(d_ee.hasTerm(atom[0]));
      Assert(d_ee.hasTerm(atom[1]));
      if (!polarity)
      {
        AlwaysAssert(d_ee.areDisequal(atom[0], atom[1], true));
      }
      d_ee.explainEquality(atom[0], atom[1], polarity, tassumptions, pf.get());
    }
  }
  else
  {
    d_ee.explainPredicate(atom, polarity, tassumptions, pf.get());
  }
  // avoid duplicates
  for (const TNode a : tassumptions)
  {
    if (std::find(assumptions.begin(), assumptions.end(), a)
        == assumptions.end())
    {
      assumptions.push_back(a);
    }
  }
  if (d_proofsEnabled)
  {
    // FIXME: convert pf to pfn
    std::shared_ptr<ProofNode> pfn;
    d_proof.registerProof(lit,pfn.get());
  }
}

Node EqProofManager::pfAssume(Node f)
{
  std::vector<Node> children;
  std::vector<Node> args;
  args.push_back(f);
  return d_proof.registerStep(f, ProofStep::ASSUME, children, args);
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
  Node as = EqProofStepChecker::applySubstitution(a, exp);
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

Node EqProofManager::pfDisequalBySubsRewrite(Node a,
                                             Node b,
                                             const std::vector<Node>& exp,
                                             bool ensureChildren)
{
  Node eqA = pfSubsRewrite(a, exp, ensureChildren);
  Node eqB = pfSubsRewrite(b, exp, ensureChildren);
  Node eqBSymm = pfSymm(eqB, ensureChildren);

  // TODO
  return Node::null();
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
  return d_proof.registerStep(
      eqSymm, ProofStep::SYMM, children, args, ensureChildren);
}

Node EqProofManager::mkAnd(const std::vector<Node>& a)
{
  if (a.empty())
  {
    return d_true;
  }
  else if (a.size() == 1)
  {
    return a[0];
  }
  return NodeManager::currentNM()->mkNode(AND, a);
}

}  // namespace eq
}  // namespace theory
}  // namespace CVC4
