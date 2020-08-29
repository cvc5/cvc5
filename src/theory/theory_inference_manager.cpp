/*********************                                                        */
/*! \file theory_inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An inference manager for Theory
 **/

#include "theory/theory_inference_manager.h"

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

TheoryInferenceManager::TheoryInferenceManager(Theory& t,
                                               TheoryState& state,
                                               ProofNodeManager* pnm)
    : d_theory(t),
      d_theoryState(state),
      d_out(t.getOutputChannel()),
      d_ee(nullptr),
      d_pnm(pnm),
      d_keep(t.getSatContext())
{
}

void TheoryInferenceManager::setEqualityEngine(eq::EqualityEngine* ee)
{
  d_ee = ee;
  // if proofs are enabled, also make a proof equality engine to wrap ee
  if (d_pnm != nullptr)
  {
    d_pfee.reset(new eq::ProofEqEngine(d_theoryState.getSatContext(),
                                       d_theoryState.getUserContext(),
                                       *d_ee,
                                       d_pnm));
  }
}

void TheoryInferenceManager::conflictEqConstantMerge(TNode a, TNode b)
{
  if (!d_theoryState.isInConflict())
  {
    TrustNode tconf = explainConflictEqConstantMerge(a, b);
    d_theoryState.notifyInConflict();
    d_out.trustedConflict(tconf);
  }
}

void TheoryInferenceManager::conflict(TNode conf)
{
  if (!d_theoryState.isInConflict())
  {
    d_theoryState.notifyInConflict();
    d_out.conflict(conf);
  }
}

void TheoryInferenceManager::trustedConflict(TrustNode tconf)
{
  if (!d_theoryState.isInConflict())
  {
    d_theoryState.notifyInConflict();
    d_out.trustedConflict(tconf);
  }
}

bool TheoryInferenceManager::propagateLit(TNode lit)
{
  // If already in conflict, no more propagation
  if (d_theoryState.isInConflict())
  {
    return false;
  }
  // Propagate out
  bool ok = d_out.propagate(lit);
  if (!ok)
  {
    d_theoryState.notifyInConflict();
  }
  return ok;
}

TrustNode TheoryInferenceManager::explainLit(TNode lit)
{
  if (d_pfee != nullptr)
  {
    return d_pfee->explain(lit);
  }
  if (d_ee != nullptr)
  {
    Node exp = d_ee->mkExplainLit(lit);
    return TrustNode::mkTrustPropExp(lit, exp, nullptr);
  }
  Unimplemented() << "Inference manager for " << d_theory.getId()
                  << " was asked to explain a propagation but doesn't have an "
                     "equality engine or implement the "
                     "TheoryInferenceManager::explainLit interface!";
}

TrustNode TheoryInferenceManager::explainConflictEqConstantMerge(TNode a,
                                                                 TNode b)
{
  Node lit = a.eqNode(b);
  if (d_pfee != nullptr)
  {
    return d_pfee->explain(lit);
  }
  if (d_ee != nullptr)
  {
    Node conf = d_ee->mkExplainLit(lit);
    return TrustNode::mkTrustConflict(conf, nullptr);
  }
  Unimplemented() << "Inference manager for " << d_theory.getId()
                  << " mkTrustedConflictEqConstantMerge";
}

LemmaStatus TheoryInferenceManager::lemma(TNode lem, LemmaProperty p)
{
  return d_out.lemma(lem, p);
}

LemmaStatus TheoryInferenceManager::trustedLemma(const TrustNode& tlem,
                                                 LemmaProperty p)
{
  return d_out.trustedLemma(tlem, p);
}

void TheoryInferenceManager::assertInternalFact(TNode atom, bool pol, TNode exp)
{
  processInternalFact(atom, pol, PfRule::ASSUME, {exp}, {});
}

void TheoryInferenceManager::assertInternalFact(TNode atom,
                                                bool pol,
                                                PfRule id,
                                                const std::vector<Node>& exp,
                                                const std::vector<Node>& args)
{
  processInternalFact(atom, pol, id, exp, args);
}

void TheoryInferenceManager::processInternalFact(TNode atom,
                                                 bool pol,
                                                 PfRule id,
                                                 const std::vector<Node>& exp,
                                                 const std::vector<Node>& args)
{
  // call the pre-notify fact method with preReg = false, isInternal = true
  if (d_theory.preNotifyFact(atom, pol, fact, false, true))
  {
    // handled in a theory-specific way that doesn't require equality engine
    return;
  }
  Assert(d_ee != nullptr);
  Trace("infer-manager") << "TheoryInferenceManager::assertInternalFact: "
                         << fact << std::endl;
  if (atom.getKind() == kind::EQUAL)
  {
    d_ee->assertEquality(atom, pol, fact);
  }
  else
  {
    d_ee->assertPredicate(atom, pol, fact);
  }
  // call the notify fact method with isInternal = true
  d_theory.notifyFact(atom, pol, fact, true);
  Trace("infer-manager")
      << "TheoryInferenceManager::finished assertInternalFact" << std::endl;
  // Must reference count the equality and its explanation, which is not done
  // by the equality engine. Notice that we do *not* need to do this for
  // external assertions, which enter as facts in theory check.
  d_keep.insert(atom);
  d_keep.insert(fact);
}

void TheoryInferenceManager::explain(TNode n, std::vector<TNode>& assumptions)
{
  if (n.getKind() == kind::AND)
  {
    for (const Node& nc : n)
    {
      d_ee->explainLit(nc, assumptions);
    }
  }
  else
  {
    d_ee->explainLit(n, assumptions);
  }
}

Node TheoryInferenceManager::mkExplain(TNode n)
{
  std::vector<TNode> assumptions;
  explain(n, assumptions);
  Node ret;
  if (assumptions.empty())
  {
    ret = NodeManager::currentNM()->mkConst(true);
  }
  else if (assumptions.size() == 1)
  {
    ret = assumptions[0];
  }
  else
  {
    ret = NodeManager::currentNM()->mkNode(kind::AND, assumptions);
  }
  return ret;
}

}  // namespace theory
}  // namespace CVC4
