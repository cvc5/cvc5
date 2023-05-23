/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An inference manager for Theory.
 */

#include "theory/theory_inference_manager.h"

#include "options/proof_options.h"
#include "proof/annotation_proof_generator.h"
#include "proof/eager_proof_generator.h"
#include "theory/builtin/proof_checker.h"
#include "theory/inference_id_proof_annotator.h"
#include "theory/output_channel.h"
#include "theory/rewriter.h"
#include "theory/theory.h"
#include "theory/theory_state.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/proof_equality_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

TheoryInferenceManager::TheoryInferenceManager(Env& env,
                                               Theory& t,
                                               TheoryState& state,
                                               const std::string& statsName,
                                               bool cacheLemmas)
    : EnvObj(env),
      d_theory(t),
      d_theoryState(state),
      d_out(t.getOutputChannel()),
      d_ee(nullptr),
      d_decManager(nullptr),
      d_pfee(nullptr),
      d_cacheLemmas(cacheLemmas),
      d_keep(context()),
      d_lemmasSent(userContext()),
      d_numConflicts(0),
      d_numCurrentLemmas(0),
      d_numCurrentFacts(0),
      d_conflictIdStats(statisticsRegistry().registerHistogram<InferenceId>(
          statsName + "inferencesConflict")),
      d_factIdStats(statisticsRegistry().registerHistogram<InferenceId>(
          statsName + "inferencesFact")),
      d_lemmaIdStats(statisticsRegistry().registerHistogram<InferenceId>(
          statsName + "inferencesLemma"))
{
  // don't add true lemma
  Node truen = NodeManager::currentNM()->mkConst(true);
  d_lemmasSent.insert(truen);

  if (isProofEnabled())
  {
    context::UserContext* u = userContext();
    ProofNodeManager* pnm = env.getProofNodeManager();
    d_defaultPg.reset(
        new EagerProofGenerator(env, u, statsName + "EagerProofGenerator"));
    if (options().proof.proofAnnotate)
    {
      d_iipa.reset(new InferenceIdProofAnnotator(pnm, u));
      d_apg.reset(new AnnotationProofGenerator(
          pnm, u, statsName + "AnnotationProofGenerator"));
    }
  }
}

TheoryInferenceManager::~TheoryInferenceManager()
{
}

void TheoryInferenceManager::setEqualityEngine(eq::EqualityEngine* ee)
{
  d_ee = ee;
  // if proofs are enabled, also make a proof equality engine to wrap ee
  // if it is non-null. If its proof equality engine has already been assigned,
  // use it. This is to ensure that all theories use the same proof equality
  // engine when in ee-mode=central.
  if (isProofEnabled() && d_ee != nullptr)
  {
    d_pfee = d_ee->getProofEqualityEngine();
    if (d_pfee == nullptr)
    {
      d_pfeeAlloc = std::make_unique<eq::ProofEqEngine>(d_env, *d_ee);
      d_pfee = d_pfeeAlloc.get();
      d_ee->setProofEqualityEngine(d_pfee);
    }
  }
}

void TheoryInferenceManager::setDecisionManager(DecisionManager* dm)
{
  d_decManager = dm;
}

bool TheoryInferenceManager::isProofEnabled() const
{
  return d_env.isTheoryProofProducing();
}

void TheoryInferenceManager::reset()
{
  d_numConflicts = 0;
  d_numCurrentLemmas = 0;
  d_numCurrentFacts = 0;
}

bool TheoryInferenceManager::hasSent() const
{
  return d_theoryState.isInConflict() || d_numCurrentLemmas > 0
         || d_numCurrentFacts > 0;
}

eq::ProofEqEngine* TheoryInferenceManager::getProofEqEngine() { return d_pfee; }

void TheoryInferenceManager::conflictEqConstantMerge(TNode a, TNode b)
{
  if (!d_theoryState.isInConflict())
  {
    TrustNode tconf = explainConflictEqConstantMerge(a, b);
    trustedConflict(tconf, InferenceId::EQ_CONSTANT_MERGE);
  }
}

void TheoryInferenceManager::conflict(TNode conf, InferenceId id)
{
  TrustNode tconf = TrustNode::mkTrustConflict(conf, nullptr);
  return trustedConflict(tconf, id);
}

void TheoryInferenceManager::trustedConflict(TrustNode tconf, InferenceId id)
{
  Assert(id != InferenceId::UNKNOWN)
      << "Must provide an inference id for conflict";
  d_conflictIdStats << id;
  resourceManager()->spendResource(id);
  Trace("im") << "(conflict " << id << " " << tconf.getProven() << ")"
              << std::endl;
  // annotate if the annotation proof generator is active
  if (d_apg != nullptr)
  {
    tconf = annotateId(tconf, id, true);
  }
  d_out.trustedConflict(tconf);
  ++d_numConflicts;
}

void TheoryInferenceManager::conflictExp(InferenceId id,
                                         PfRule pfr,
                                         const std::vector<Node>& exp,
                                         const std::vector<Node>& args)
{
  if (!d_theoryState.isInConflict())
  {
    // make the trust node
    TrustNode tconf = mkConflictExp(pfr, exp, args);
    // send it on the output channel
    trustedConflict(tconf, id);
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

void TheoryInferenceManager::conflictExp(InferenceId id,
                                         const std::vector<Node>& exp,
                                         ProofGenerator* pg)
{
  if (!d_theoryState.isInConflict())
  {
    // make the trust node
    TrustNode tconf = mkConflictExp(exp, pg);
    // send it on the output channel
    trustedConflict(tconf, id);
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

bool TheoryInferenceManager::lemma(TNode lem, InferenceId id, LemmaProperty p)
{
  TrustNode tlem = TrustNode::mkTrustLemma(lem, nullptr);
  return trustedLemma(tlem, id, p);
}

bool TheoryInferenceManager::trustedLemma(const TrustNode& tlem,
                                          InferenceId id,
                                          LemmaProperty p)
{
  // if the policy says to cache lemmas, check the cache and return false if
  // we are a duplicate
  if (d_cacheLemmas)
  {
    if (!cacheLemma(tlem.getNode(), p))
    {
      return false;
    }
  }
  Assert(id != InferenceId::UNKNOWN)
      << "Must provide an inference id for lemma";
  d_lemmaIdStats << id;
  resourceManager()->spendResource(id);
  Trace("im") << "(lemma " << id << " " << tlem.getProven() << ")" << std::endl;
  // shouldn't send trivially true or false lemmas
  Assert(!rewrite(tlem.getProven()).isConst());
  d_numCurrentLemmas++;
  // annotate if the annotation proof generator is active
  if (d_apg != nullptr)
  {
    TrustNode tlema = annotateId(tlem, id);
    d_out.trustedLemma(tlema, p);
  }
  else
  {
    d_out.trustedLemma(tlem, p);
  }
  return true;
}

bool TheoryInferenceManager::lemmaExp(Node conc,
                                      InferenceId id,
                                      PfRule pfr,
                                      const std::vector<Node>& exp,
                                      const std::vector<Node>& noExplain,
                                      const std::vector<Node>& args,
                                      LemmaProperty p)
{
  // make the trust node
  TrustNode trn = mkLemmaExp(conc, pfr, exp, noExplain, args);
  // send it on the output channel
  return trustedLemma(trn, id, p);
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
                                      InferenceId id,
                                      const std::vector<Node>& exp,
                                      const std::vector<Node>& noExplain,
                                      ProofGenerator* pg,
                                      LemmaProperty p)
{
  // make the trust node
  TrustNode trn = mkLemmaExp(conc, exp, noExplain, pg);
  // send it on the output channel
  return trustedLemma(trn, id, p);
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
  Node rewritten = rewrite(lem);
  return d_lemmasSent.find(rewritten) != d_lemmasSent.end();
}

uint32_t TheoryInferenceManager::numSentLemmas() const
{
  return d_numCurrentLemmas;
}

bool TheoryInferenceManager::hasSentLemma() const
{
  return d_numCurrentLemmas != 0;
}

bool TheoryInferenceManager::assertInternalFact(TNode atom,
                                                bool pol,
                                                InferenceId id,
                                                TNode exp)
{
  return processInternalFact(
      atom, pol, id, PfRule::UNKNOWN, {exp}, {}, nullptr);
}

bool TheoryInferenceManager::assertInternalFact(TNode atom,
                                                bool pol,
                                                InferenceId id,
                                                PfRule pfr,
                                                const std::vector<Node>& exp,
                                                const std::vector<Node>& args)
{
  Assert(pfr != PfRule::UNKNOWN);
  return processInternalFact(atom, pol, id, pfr, exp, args, nullptr);
}

bool TheoryInferenceManager::assertInternalFact(TNode atom,
                                                bool pol,
                                                InferenceId id,
                                                const std::vector<Node>& exp,
                                                ProofGenerator* pg)
{
  return processInternalFact(atom, pol, id, PfRule::ASSUME, exp, {}, pg);
}

bool TheoryInferenceManager::processInternalFact(TNode atom,
                                                 bool pol,
                                                 InferenceId iid,
                                                 PfRule id,
                                                 const std::vector<Node>& exp,
                                                 const std::vector<Node>& args,
                                                 ProofGenerator* pg)
{
  Assert(iid != InferenceId::UNKNOWN)
      << "Must provide an inference id for fact";
  d_factIdStats << iid;
  resourceManager()->spendResource(iid);
  // make the node corresponding to the explanation
  Node expn = NodeManager::currentNM()->mkAnd(exp);
  Trace("im") << "(fact " << iid << " " << (pol ? Node(atom) : atom.notNode())
              << " " << expn << ")" << std::endl;
  // call the pre-notify fact method with preReg = false, isInternal = true
  if (d_theory.preNotifyFact(atom, pol, expn, false, true))
  {
    // Handled in a theory-specific way that doesn't require equality engine,
    // notice we return true, indicating that the fact was processed.
    return true;
  }
  Assert(d_ee != nullptr);
  Trace("infer-manager") << "TheoryInferenceManager::assertInternalFact: "
                         << (pol ? Node(atom) : atom.notNode()) << " from "
                         << expn << " / " << iid << " " << id << std::endl;
  if (Configuration::isAssertionBuild())
  {
    // check that all facts hold in the equality engine, to ensure that we
    // aren't processing a stale fact
    std::vector<Node> expc = exp;
    for (size_t i = 0; i < expc.size(); i++)
    {
      Node e = expc[i];
      bool epol = e.getKind() != NOT;
      Node eatom = epol ? e : e[0];
      Trace("infer-manager")
          << "...check " << eatom << " " << epol << std::endl;
      if (eatom.getKind() == AND)
      {
        Assert(epol);
        for (const Node& ea : eatom)
        {
          expc.push_back(ea);
        }
        continue;
      }
      else if (eatom.getKind() == EQUAL)
      {
        Assert(d_ee->hasTerm(eatom[0]));
        Assert(d_ee->hasTerm(eatom[1]));
        Assert(!epol || d_ee->areEqual(eatom[0], eatom[1]));
        Assert(epol || d_ee->areDisequal(eatom[0], eatom[1], false));
      }
      else
      {
        Assert(d_ee->hasTerm(eatom));
        Assert(d_ee->areEqual(eatom, NodeManager::currentNM()->mkConst(epol)));
      }
    }
  }
  d_numCurrentFacts++;
  // Now, assert the fact. How to do so depends on whether proofs are enabled.
  bool ret = false;
  if (d_pfee == nullptr)
  {
    Trace("infer-manager") << "...assert without proofs..." << std::endl;
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
    Assert(id != PfRule::UNKNOWN);
    Trace("infer-manager") << "...assert with proofs..." << std::endl;
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
      << "TheoryInferenceManager::finished assertInternalFact, ret=" << ret
      << std::endl;
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
  Node rewritten = rewrite(lem);
  if (d_lemmasSent.find(rewritten) != d_lemmasSent.end())
  {
    return false;
  }
  d_lemmasSent.insert(rewritten);
  return true;
}

TrustNode TheoryInferenceManager::annotateId(const TrustNode& trn,
                                             InferenceId id,
                                             bool isConflict)
{
  Assert(d_iipa != nullptr && d_apg != nullptr);
  Node lemma = trn.getProven();
  TrustNode trna = trn;
  // ensure we have a proof generator, make trusted theory lemma if not
  if (trn.getGenerator() == nullptr)
  {
    Node tidn =
        builtin::BuiltinProofRuleChecker::mkTheoryIdNode(d_theory.getId());
    trna = d_defaultPg->mkTrustNode(
        trn.getNode(), PfRule::THEORY_LEMMA, {}, {lemma, tidn}, isConflict);
  }
  d_iipa->setAnnotation(lemma, id);
  return d_apg->transform(trna, d_iipa.get());
}

DecisionManager* TheoryInferenceManager::getDecisionManager()
{
  return d_decManager;
}

void TheoryInferenceManager::requirePhase(TNode n, bool pol)
{
  Node en = d_theoryState.getValuation().ensureLiteral(n);
  return d_out.requirePhase(en, pol);
}

void TheoryInferenceManager::spendResource(Resource r)
{
  d_out.spendResource(r);
}

void TheoryInferenceManager::safePoint(Resource r)
{
  d_out.safePoint(r);
}

void TheoryInferenceManager::setModelUnsound(IncompleteId id)
{
  d_out.setModelUnsound(id);
}

void TheoryInferenceManager::setRefutationUnsound(IncompleteId id)
{
  d_out.setRefutationUnsound(id);
}

void TheoryInferenceManager::notifyInConflict()
{
  d_theoryState.notifyInConflict();
}

}  // namespace theory
}  // namespace cvc5::internal
