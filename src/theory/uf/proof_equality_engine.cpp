/*********************                                                        */
/*! \file proof_equality_engine.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of the proof-producing equality engine
 **/

#include "theory/uf/proof_equality_engine.h"

#include "theory/rewriter.h"
#include "theory/uf/proof_checker.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace eq {

ProofEqEngine::ProofEqEngine(context::Context* c,
                             context::UserContext* u,
                             EqualityEngine& ee,
                             ProofNodeManager* pnm,
                             bool pfEnabled)
    : EagerProofGenerator(u, pnm),
      d_ee(ee),
      d_proof(pnm, c),
      d_keep(c),
      d_pfEnabled(pfEnabled)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool ProofEqEngine::assertAssume(Node lit)
{
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  if (d_pfEnabled)
  {
    // first, add the step in the proof
    std::vector<Node> exp;
    std::vector<Node> args;
    args.push_back(lit);
    if (!d_proof.addStep(lit, PfRule::ASSUME, exp, args))
    {
      // failed to add step
      return false;
    }
  }

  // second, assert it to the equality engine, where it is its own explanation
  assertInternal(atom, polarity, lit);

  return true;
}

bool ProofEqEngine::assertFact(Node lit,
                               PfRule id,
                               const std::vector<Node>& exp,
                               const std::vector<Node>& args)
{
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // first, register the step in the proof
  if (d_pfEnabled)
  {
    if (!d_proof.addStep(lit, id, exp, args))
    {
      // failed to register step
      return false;
    }
  }

  // second, assert it to the equality engine
  Node reason = mkAnd(exp);
  assertInternal(atom, polarity, reason);

  return true;
}

bool ProofEqEngine::assertFact(Node lit,
                               PfRule id,
                               Node exp,
                               const std::vector<Node>& args)
{
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  if (!d_pfEnabled)
  {
    assertInternal(atom, polarity, exp);
    return true;
  }
  std::vector<Node> expv;
  if (exp != d_true)
  {
    if (exp.getKind() == AND)
    {
      for (const Node& e : expv)
      {
        expv.push_back(e);
      }
    }
    else
    {
      expv.push_back(e);
    }
  }
  return assertFact(lit, id, expv, args);
}

bool ProofEqEngine::assertFact(Node lit, ProofNode* p)
{
  Assert(p != nullptr);
  const std::vector<std::shared_ptr<ProofNode>>& children = p->getChildren();
  std::vector<Node> exp;
  for (const std::shared_ptr<ProofNode>& pc : p)
  {
    Node litc = pc->getResult();
    exp.push_back(litc);
    // must add the proof
    d_proof.addProof(litc, pc.get());
  }
  return assertFact(lit, p->getId(), exp, p->getArguments());
}

TrustNode ProofEqEngine::getConflict()
{
  // TODO
}

TrustNode ProofEqEngine::assertConflict(PfRule id, const std::vector<Node>& exp)
{
  std::vector<Node> args;
  return assertConflict(id, exp, args);
}

TrustNode ProofEqEngine::assertConflict(PfRule id,
                                        const std::vector<Node>& exp,
                                        const std::vector<Node>& args)
{
  // conflict is same as proof of false
  std::vector<Node> expn;
  return assertLemma(d_false, id, exp, expn, args);
}

TrustNode assertLemma(Node conc,
                      PfRule id,
                      const std::vector<Node>& exp,
                      const std::vector<Node>& expn,
                      const std::vector<Node>& args)
{
  Assert(d_conc != d_true);
  if (d_pfEnabled)
  {
    // Register the proof step.
    std::vector<Node> expAll;
    expAll.insert(expAll.end(), exp.begin(), exp.end());
    expAll.insert(expAll.end(), expn.begin(), expn.end());
    if (!d_proof.addStep(conc, id, expAll, args))
    {
      // a step went wrong, e.g. during checking
      Assert(false) << "ProofEqEngine::assertConflict: register proof step";
      return TrustNode::null();
    }
  }

  // get the explanation, with proofs
  std::vector<TNode> assumps;
  for (const Node& e : exp)
  {
    explainWithProof(e, assumps);
  }
  assumps.insert(assumps.end(), expn.begin(), expn.end());

  // We are a conflict if the conclusion is false and all literals are
  // explained.
  bool isConflict = conc == d_false && expn.empty();

  // make the conflict or lemma
  Node formula = mkAnd(assumps);
  if (!isConflict)
  {
    formula = formula == d_false ? conc : nm->mkNode(IMPLIES, formula, conc);
  }

  if (d_pfEnabled)
  {
    // get the proof for false
    std::shared_ptr<ProofNode> pf = mkProofForFact(conc);
    if (pf == nullptr)
    {
      // should have existed
      Assert(false) << "ProofEqEngine::assertConflict: failed to get proof";
      return TrustNode::null();
    }
    // set the proof for the conflict or lemma, which can be queried later
    if (isConflict)
    {
      setProofForConflict(formula, pf);
    }
    else
    {
      setProofForLemma(formula, pf);
    }
  }
  // we can provide a proof for conflict or lemma
  if (isConflict)
  {
    return TrustNode::mkTrustConflict(formula, this);
  }
  return TrustNode::mkTrustLemma(formula, this);
}

std::shared_ptr<ProofNode> ProofEqEngine::mkProofForFact(Node lit) const
{
  std::shared_ptr<ProofNode> p = d_proof.getProof(lit);
  if (p == nullptr)
  {
    return nullptr;
  }
  // clone it so that we have a fresh copy
  return p->clone();
}

void ProofEqEngine::assertInternal(Node atom, bool polarity, TNode reason)
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

void ProofEqEngine::explainWithProof(Node lit, std::vector<TNode>& assumps)
{
  std::shared_ptr<eq::EqProof> pf =
      d_pfEnabled ? std::make_shared<eq::EqProof>() : nullptr;
  bool polarity = lit.getKind() != NOT;
  TNode atom = polarity ? lit : lit[0];
  std::vector<TNode> tassumps;
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
      d_ee.explainEquality(atom[0], atom[1], polarity, tassumps, pf.get());
    }
  }
  else
  {
    d_ee.explainPredicate(atom, polarity, tassumps, pf.get());
  }
  // avoid duplicates
  for (const TNode a : tassumps)
  {
    if (std::find(assumps.begin(), assumps.end(), a) == assumps.end())
    {
      assumps.push_back(a);
    }
  }
  if (d_pfEnabled)
  {
    // add the steps in the equality engine proof to the Proof
    pf->addTo(d_proof.get());
  }
}

Node ProofEqEngine::mkAnd(const std::vector<Node>& a)
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

Node ProofEqEngine::mkAnd(const std::vector<TNode>& a)
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
