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
      d_pnm(pnm),
      d_proof(pnm, c),
      d_keep(c),
      d_pfEnabled(pfEnabled)
{
  NodeManager* nm = NodeManager::currentNM();
  d_true = nm->mkConst(true);
  d_false = nm->mkConst(false);
}

bool ProofEqEngine::assertAssume(TNode lit)
{
  TNode atom = lit.getKind() == NOT ? lit[0] : lit;
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
  // first, register the step in the proof
  if (d_pfEnabled)
  {
    if (!d_proof.addStep(lit, id, exp, args))
    {
      // failed to register step
      return false;
    }
  }

  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // second, assert it to the equality engine
  Node reason = mkAnd(exp);
  assertInternal(atom, polarity, reason);
  // must reference count the new atom and explanation
  d_keep.insert(atom);
  d_keep.insert(reason);

  return true;
}

bool ProofEqEngine::assertFact(Node lit,
                               PfRule id,
                               Node exp,
                               const std::vector<Node>& args)
{
  // first, register the step in the proof
  if (d_pfEnabled)
  {
    // must extract the explanation as a vector
    std::vector<Node> expv;
    if (exp != d_true)
    {
      if (exp.getKind() == AND)
      {
        for (const Node& e : expv)
        {
          Assert(e.getKind() != AND);
          expv.push_back(e);
        }
      }
      else
      {
        expv.push_back(exp);
      }
    }
    if (!d_proof.addStep(lit, id, expv, args))
    {
      // failed to register step
      return false;
    }
  }
  Node atom = lit.getKind() == NOT ? lit[0] : lit;
  bool polarity = lit.getKind() != NOT;

  // second, assert it to the equality engine
  assertInternal(atom, polarity, exp);
  d_keep.insert(atom);
  d_keep.insert(exp);

  return true;
}

// could combine proofs with this
/*
bool ProofEqEngine::assertFact(Node lit, ProofNode* p)
{
  Assert(p != nullptr);
  const std::vector<std::shared_ptr<ProofNode>>& children = p->getChildren();
  std::vector<Node> exp;
  for (const std::shared_ptr<ProofNode>& pc : children)
  {
    Node litc = pc->getResult();
    exp.push_back(litc);
    // must add the proof
    d_proof.addProof(litc, pc.get());
  }
  return assertFact(lit, p->getId(), exp, p->getArguments());
}
*/

TrustNode ProofEqEngine::assertConflict(Node lit)
{
  std::vector<TNode> assumps;
  explainWithProof(lit, assumps);
  return ensureProofForFact(d_false, assumps, true);
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
  return assertLemma(d_false, id, exp, exp, args);
}

TrustNode ProofEqEngine::assertLemma(Node conc,
                                     PfRule id,
                                     const std::vector<Node>& exp,
                                     const std::vector<Node>& toExplain,
                                     const std::vector<Node>& args)
{
  Trace("pfee") << "pfee::assertLemma " << conc << " " << id << std::endl;
  Trace("pfee") << "        exp = " << exp << std::endl;
  Trace("pfee") << "  toExplain = " << toExplain << std::endl;
  Trace("pfee") << "       args = " << args << std::endl;
  Assert(conc != d_true);
  if (d_pfEnabled)
  {
    // Register the proof step.
    if (!d_proof.addStep(conc, id, exp, args))
    {
      // a step went wrong, e.g. during checking
      Assert(false) << "pfee::assertConflict: register proof step";
      return TrustNode::null();
    }
  }
  // We are a conflict if the conclusion is false and all literals are
  // explained.
  bool isConflict = conc == d_false;

  // get the explanation, with proofs
  std::vector<TNode> assumps;
  std::vector<Node> expn;
  for (const Node& e : exp)
  {
    if (std::find(toExplain.begin(), toExplain.end(), e) != toExplain.end())
    {
      explainWithProof(e, assumps);
    }
    else
    {
      // it did not have a proof; it was an assumption of the previous rule
      assumps.push_back(e);
      // it is not a conflict, since it may involve new literals
      isConflict = false;
    }
  }
  return ensureProofForFact(conc, assumps, isConflict);
}

TrustNode ProofEqEngine::ensureProofForFact(Node conc,
                                            const std::vector<TNode>& assumps,
                                            bool isConflict)
{
  Trace("pfee-proof") << std::endl;
  Trace("pfee-proof") << "pfee::ensureProofForFact: input " << conc << " via "
                      << assumps << ", isConflict=" << isConflict << std::endl;
  // make the conflict or lemma
  Node formula = mkAnd(assumps);
  if (!isConflict)
  {
    NodeManager* nm = NodeManager::currentNM();
    formula = formula == d_true ? conc : nm->mkNode(IMPLIES, formula, conc);
  }
  Trace("pfee-proof") << "pfee::ensureProofForFact: formula is " << formula
                      << std::endl;
  ProofGenerator* pfg = nullptr;
  if (d_pfEnabled)
  {
    Trace("pfee-proof") << "pfee::ensureProofForFact: make proof for fact"
                        << std::endl;
    // get the proof for conc
    std::shared_ptr<ProofNode> pfConc = mkProofForFact(conc);
    if (pfConc == nullptr)
    {
      Trace("pfee-proof")
          << "pfee::ensureProofForFact: failed to make proof for fact"
          << std::endl
          << std::endl;
      // should have existed
      Assert(false) << "pfee::assertConflict: failed to get proof for " << conc;
      return TrustNode::null();
    }
    Trace("pfee-proof") << "pfee::ensureProofForFact: add scope" << std::endl;
    // Wrap the proof in a SCOPE. Notice that we have an expected conclusion
    // (formula) which we pass to mkNode, which can check it if it wants. Its
    // arguments are the free assumptions of pfConc.
    std::vector<Node> args;
    pfConc->getFreeAssumptions(args);
    std::shared_ptr<ProofNode> pf =
        d_pnm->mkNode(PfRule::SCOPE, pfConc, args, formula);
    if (Trace.isOn("pfee-proof"))
    {
      Trace("pfee-proof") << "pfee::ensureProofForFact: printing proof"
                          << std::endl;
      std::stringstream ss;
      pf->printDebug(ss);
      Trace("pfee-proof") << "pfee::ensureProofForFact: Proof is " << ss.str()
                          << std::endl;
    }
    // should always succeed, since assumptions should be closed
    Assert(pf != nullptr);
    // should be a closed proof now
    Assert(pf->isClosed());
    // set the proof for the conflict or lemma, which can be queried later
    if (isConflict)
    {
      setProofForConflict(formula, pf);
    }
    else
    {
      setProofForLemma(formula, pf);
    }
    pfg = this;
  }
  Trace("pfee-proof") << "pfee::ensureProofForFact: finish" << std::endl
                      << std::endl;
  // we can provide a proof for conflict or lemma
  if (isConflict)
  {
    return TrustNode::mkTrustConflict(formula, pfg);
  }
  return TrustNode::mkTrustLemma(formula, pfg);
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

void ProofEqEngine::assertInternal(TNode atom, bool polarity, TNode reason)
{
  Trace("pfee-debug") << "pfee::assertInternal: " << atom << " " << polarity
                      << " " << reason << std::endl;
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
  Trace("pfee-proof") << "pfee::explainWithProof: " << lit << " via " << assumps
                      << std::endl;
  bool polarity = lit.getKind() != NOT;
  TNode atom = polarity ? lit : lit[0];
  Assert(atom.getKind() != AND);
  std::vector<TNode> tassumps;
  if (atom.getKind() == EQUAL)
  {
    if (atom[0] != atom[1])
    {
      Assert(d_ee.hasTerm(atom[0]));
      Assert(d_ee.hasTerm(atom[1]));
      if (!polarity)
      {
        // ensure the explanation exists
        AlwaysAssert(d_ee.areDisequal(atom[0], atom[1], true));
      }
      else
      {
        // Assert(d_ee.areEqual(atom[0], atom[1]));
      }
      d_ee.explainEquality(atom[0], atom[1], polarity, tassumps, pf.get());
    }
  }
  else
  {
    Assert(d_ee.hasTerm(atom));
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
    Trace("pfee-proof") << "pfee::explainWithProof: add to proof" << std::endl;
    // add the steps in the equality engine proof to the Proof
    pf->addToProof(&d_proof);
  }
  Trace("pfee-proof") << "pfee::explainWithProof: finished" << std::endl;
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

std::ostream& operator<<(std::ostream& out, const ProofInferInfo& pii)
{
  out << "(proof-infer " << pii.d_rule << " " << pii.d_conc;
  if (!pii.d_children.empty())
  {
    out << " :children (" << pii.d_children << ")";
  }
  if (!pii.d_args.empty())
  {
    out << " :args (" << pii.d_args << ")";
  }
  if (!pii.d_childrenExp.empty())
  {
    out << " :childrenExp (" << pii.d_childrenExp << ")";
  }
  out << ")";
  return out;
}

}  // namespace eq
}  // namespace theory
}  // namespace CVC4
