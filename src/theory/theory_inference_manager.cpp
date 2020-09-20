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
      d_keep(t.getSatContext()),
      d_lemmasSent(t.getUserContext()),
      d_numCurrentLemmas(0),
      d_numCurrentFacts(0)
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

bool TheoryInferenceManager::isProofEnabled() const { return d_pnm != nullptr; }

void TheoryInferenceManager::reset()
{
  d_numCurrentLemmas = 0;
  d_numCurrentFacts = 0;
}

bool TheoryInferenceManager::hasSent() const
{
  return d_theoryState.isInConflict() || d_numCurrentLemmas > 0
         || d_numCurrentFacts > 0;
}

eq::ProofEqEngine* TheoryInferenceManager::getProofEqEngine()
{
  return d_pfee.get();
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

void TheoryInferenceManager::conflictExp(PfRule id,
                                         const std::vector<Node>& exp,
                                         const std::vector<Node>& args)
{
  if (!d_theoryState.isInConflict())
  {
    // make the trust node
    TrustNode tconf = mkConflictExp(id, exp, args);
    // send it on the output channel
    trustedConflict(tconf);
  }
}

TrustNode TheoryInferenceManager::mkConflictExp(PfRule id,
                                                const std::vector<Node>& exp,
                                                const std::vector<Node>& args)
{
  if (d_pfee != nullptr)
  {
    // use proof equality engine to construct the trust node
    return d_pfee->assertConflict(id, exp, args);
  }
  // version without proofs
  Node conf = mkExplainPartial(exp, {});
  return TrustNode::mkTrustConflict(conf, nullptr);
}

void TheoryInferenceManager::conflictExp(const std::vector<Node>& exp,
                                         ProofGenerator* pg)
{
  if (!d_theoryState.isInConflict())
  {
    // make the trust node
    TrustNode tconf = mkConflictExp(exp, pg);
    // send it on the output channel
    trustedConflict(tconf);
  }
}

TrustNode TheoryInferenceManager::mkConflictExp(const std::vector<Node>& exp,
                                                ProofGenerator* pg)
{
  if (d_pfee != nullptr)
  {
    Assert(pg != nullptr);
    // use proof equality engine to construct the trust node
    return d_pfee->assertConflict(exp, pg);
  }
  // version without proofs
  Node conf = mkExplainPartial(exp, {});
  return TrustNode::mkTrustConflict(conf, nullptr);
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
    return d_pfee->assertConflict(lit);
  }
  if (d_ee != nullptr)
  {
    Node conf = d_ee->mkExplainLit(lit);
    return TrustNode::mkTrustConflict(conf, nullptr);
  }
  Unimplemented() << "Inference manager for " << d_theory.getId()
                  << " mkTrustedConflictEqConstantMerge";
}

bool TheoryInferenceManager::lemma(TNode lem, LemmaProperty p, bool doCache)
{
  TrustNode tlem = TrustNode::mkTrustLemma(lem, nullptr);
  return trustedLemma(tlem, p, doCache);
}

bool TheoryInferenceManager::trustedLemma(const TrustNode& tlem,
                                          LemmaProperty p,
                                          bool doCache)
{
  if (doCache)
  {
    if (!cacheLemma(tlem.getNode(), p))
    {
      return false;
    }
  }
  d_numCurrentLemmas++;
  d_out.trustedLemma(tlem, p);
  return true;
}

bool TheoryInferenceManager::lemmaExp(Node conc,
                                      PfRule id,
                                      const std::vector<Node>& exp,
                                      const std::vector<Node>& noExplain,
                                      const std::vector<Node>& args,
                                      LemmaProperty p,
                                      bool doCache)
{
  // make the trust node
  TrustNode trn = mkLemmaExp(conc, id, exp, noExplain, args);
  // send it on the output channel
  return trustedLemma(trn, p, doCache);
}

TrustNode TheoryInferenceManager::mkLemmaExp(Node conc,
                                             PfRule id,
                                             const std::vector<Node>& exp,
                                             const std::vector<Node>& noExplain,
                                             const std::vector<Node>& args)
{
  if (d_pfee != nullptr)
  {
    // make the trust node from the proof equality engine
    return d_pfee->assertLemma(conc, id, exp, noExplain, args);
  }
  // otherwise, not using proofs, explain and make trust node
  Node ant = mkExplainPartial(exp, noExplain);
  Node lem = NodeManager::currentNM()->mkNode(kind::IMPLIES, ant, conc);
  return TrustNode::mkTrustLemma(lem, nullptr);
}

bool TheoryInferenceManager::lemmaExp(Node conc,
                                      const std::vector<Node>& exp,
                                      const std::vector<Node>& noExplain,
                                      ProofGenerator* pg,
                                      LemmaProperty p,
                                      bool doCache)
{
  // make the trust node
  TrustNode trn = mkLemmaExp(conc, exp, noExplain, pg);
  // send it on the output channel
  return trustedLemma(trn, p, doCache);
}

TrustNode TheoryInferenceManager::mkLemmaExp(Node conc,
                                             const std::vector<Node>& exp,
                                             const std::vector<Node>& noExplain,
                                             ProofGenerator* pg)
{
  if (d_pfee != nullptr)
  {
    // make the trust node from the proof equality engine
    return d_pfee->assertLemma(conc, exp, noExplain, pg);
  }
  // otherwise, not using proofs, explain and make trust node
  Node ant = mkExplainPartial(exp, noExplain);
  Node lem = NodeManager::currentNM()->mkNode(kind::IMPLIES, ant, conc);
  return TrustNode::mkTrustLemma(lem, nullptr);
}

bool TheoryInferenceManager::hasCachedLemma(TNode lem, LemmaProperty p)
{
  return d_lemmasSent.find(lem) != d_lemmasSent.end();
}

uint32_t TheoryInferenceManager::numSentLemmas() const
{
  return d_numCurrentLemmas;
}

bool TheoryInferenceManager::hasSentLemma() const
{
  return d_numCurrentLemmas != 0;
}

bool TheoryInferenceManager::assertInternalFact(TNode atom, bool pol, TNode exp)
{
  return processInternalFact(atom, pol, PfRule::UNKNOWN, {exp}, {}, nullptr);
}

bool TheoryInferenceManager::assertInternalFact(TNode atom,
                                                bool pol,
                                                PfRule id,
                                                const std::vector<Node>& exp,
                                                const std::vector<Node>& args)
{
  Assert(id != PfRule::UNKNOWN);
  return processInternalFact(atom, pol, id, exp, args, nullptr);
}

bool TheoryInferenceManager::assertInternalFact(TNode atom,
                                                bool pol,
                                                const std::vector<Node>& exp,
                                                ProofGenerator* pg)
{
  Assert(pg != nullptr);
  return processInternalFact(atom, pol, PfRule::ASSUME, exp, {}, pg);
}

bool TheoryInferenceManager::processInternalFact(TNode atom,
                                                 bool pol,
                                                 PfRule id,
                                                 const std::vector<Node>& exp,
                                                 const std::vector<Node>& args,
                                                 ProofGenerator* pg)
{
  // make the node corresponding to the explanation
  Node expn = NodeManager::currentNM()->mkAnd(exp);
  // call the pre-notify fact method with preReg = false, isInternal = true
  if (d_theory.preNotifyFact(atom, pol, expn, false, true))
  {
    // Handled in a theory-specific way that doesn't require equality engine,
    // notice we return true, indicating that the fact was processed.
    return true;
  }
  Assert(d_ee != nullptr);
  Trace("infer-manager") << "TheoryInferenceManager::assertInternalFact: "
                         << expn << std::endl;
  d_numCurrentFacts++;
  // Now, assert the fact. How to do so depends on whether proofs are enabled.
  // If no proof production, or no proof rule was given
  bool ret = false;
  if (d_pfee == nullptr || id == PfRule::UNKNOWN)
  {
    if (atom.getKind() == kind::EQUAL)
    {
      ret = d_ee->assertEquality(atom, pol, expn);
    }
    else
    {
      ret = d_ee->assertPredicate(atom, pol, expn);
    }
    // Must reference count the equality and its explanation, which is not done
    // by the equality engine. Notice that we do *not* need to do this for
    // external assertions, which enter as facts in theory check. This is also
    // not done if we are asserting to the proof equality engine, which does
    // this caching itself within ProofEqEngine::assertFact.
    d_keep.insert(atom);
    d_keep.insert(expn);
  }
  else
  {
    // Note that we reconstruct the original literal lit here, since both the
    // original literal is needed for bookkeeping proofs. It is possible to
    // optimize this so that a few less nodes are created, but at the cost
    // of a more verbose interface to proof equality engine.
    Node lit = pol ? Node(atom) : atom.notNode();
    if (pg != nullptr)
    {
      // use the proof generator interface
      ret = d_pfee->assertFact(lit, expn, pg);
    }
    else
    {
      // use the explict proof step interface
      ret = d_pfee->assertFact(lit, id, expn, args);
    }
  }
  // call the notify fact method with isInternal = true
  d_theory.notifyFact(atom, pol, expn, true);
  Trace("infer-manager")
      << "TheoryInferenceManager::finished assertInternalFact" << std::endl;
  return ret;
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
  return NodeManager::currentNM()->mkAnd(assumptions);
}

Node TheoryInferenceManager::mkExplainPartial(
    const std::vector<Node>& exp, const std::vector<Node>& noExplain)
{
  std::vector<TNode> assumps;
  for (const Node& e : exp)
  {
    if (std::find(noExplain.begin(), noExplain.end(), e) != noExplain.end())
    {
      if (std::find(assumps.begin(), assumps.end(), e) == assumps.end())
      {
        // a non-explained literal
        assumps.push_back(e);
      }
      continue;
    }
    // otherwise, explain it
    explain(e, assumps);
  }
  return NodeManager::currentNM()->mkAnd(assumps);
}

uint32_t TheoryInferenceManager::numSentFacts() const
{
  return d_numCurrentFacts;
}

bool TheoryInferenceManager::hasSentFact() const
{
  return d_numCurrentFacts != 0;
}

bool TheoryInferenceManager::cacheLemma(TNode lem, LemmaProperty p)
{
  if (d_lemmasSent.find(lem) != d_lemmasSent.end())
  {
    return false;
  }
  d_lemmasSent.insert(lem);
  return true;
}

void TheoryInferenceManager::requirePhase(TNode n, bool pol)
{
  return d_out.requirePhase(n, pol);
}

void TheoryInferenceManager::spendResource(ResourceManager::Resource r)
{
  d_out.spendResource(r);
}

void TheoryInferenceManager::safePoint(ResourceManager::Resource r)
{
  d_out.safePoint(r);
}

void TheoryInferenceManager::setIncomplete() { d_out.setIncomplete(); }

}  // namespace theory
}  // namespace CVC4
