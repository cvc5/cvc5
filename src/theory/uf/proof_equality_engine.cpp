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
                             bool pfEnabled
                            )
    : EagerProofGenerator(u), d_ee(ee), d_proof(c, pnm), d_pfEnabled(pfEnabled)
{
  NodeManager * nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool ProofEqEngine::assertAssume(Node lit)
{
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  Node ret;
  if (d_pfEnabled)
  {
    // first, register the step in the proof
    std::vector<Node> exp;
    std::vector<Node> args;
    args.push_back(lit);
    ret = d_proof.registerStep(lit, PfRule::ASSUME, exp, args);
  }
  else
  {
    ret = lit;
  }

  // second, assert it to the equality engine, where it is its own explanation
  assertInternal(atom, polarity, lit);

  Assert(lit==ret);
  return lit==ret;
}

bool ProofEqEngine::assertFact(Node lit, PfRule id, const std::vector<Node>& exp)
{
  std::vector<Node> args;
  return assertFact(lit, id, exp, args);
}

bool ProofEqEngine::assertFact(Node lit, PfRule id, const std::vector<Node>& exp, const std::vector<Node>& args)
{
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // first, register the step in the proof
  Node ret = d_pfEnabled ? d_proof.registerStep(lit, id, exp, args) : lit;

  // second, assert it to the equality engine
  Node reason = mkAnd(exp);
  assertInternal(lit, polarity, reason);
  
  // return true if the proof was accurate
  Assert(lit==ret);
  return lit==ret;
}

Node ProofEqEngine::assertConflict(PfRule id, const std::vector<Node>& exp)
{
  std::vector<Node> args;
  return assertConflict(id, exp, args);
}

Node ProofEqEngine::assertConflict(PfRule id, const std::vector<Node>& exp, const std::vector<Node>& args)
{
  if (d_pfEnabled)
  {
    // register the (conflicting) proof step
    Node ret = d_proof.registerStep(d_false, id, exp, args);
    if (ret!=d_false)
    {
      // a step went wrong, e.g. during checking
      Assert(false);
      return Node::null();
    }
  }
  
  // get the explanation
  std::vector<TNode> assumps;
  for (const Node& e : exp)
  {
    explainWithProof(e, assumps);
  }
  
  // make the conflict
  Node conf = mkAnd(assumps);
  
  if (d_pfEnabled)
  {
    // get the proof for false
    std::shared_ptr<ProofNode> pf = mkProofForFact(d_false);
    if (pf==nullptr)
    {
      return Node::null();
    }
    // set the proof for the conflict, which can be queried later
    setProofForConflict(conf, pf);
  }
  return conf;
}

std::shared_ptr<ProofNode> ProofEqEngine::mkProofForFact(Node lit) const
{
  std::shared_ptr<ProofNode> p = d_proof.getProof(lit);
  if (p==nullptr)
  {
    return nullptr;
  }
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
    // FIXME: convert pf to pfn
    std::shared_ptr<ProofNode> pfn;
    // add the given proof to the proof object constructed by this class
    d_proof.registerProof(lit, pfn);
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
