/*********************                                                        */
/*! \file engine_output_channel.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Guy Katz, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The theory engine output channel.
 **/

#include "theory/engine_output_channel.h"

#include "proof/cnf_proof.h"
#include "proof/lemma_proof.h"
#include "proof/proof_manager.h"
#include "proof/theory_proof.h"
#include "prop/prop_engine.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory_engine.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {

EngineOutputChannel::Statistics::Statistics(theory::TheoryId theory)
    : conflicts(getStatsPrefix(theory) + "::conflicts", 0),
      propagations(getStatsPrefix(theory) + "::propagations", 0),
      lemmas(getStatsPrefix(theory) + "::lemmas", 0),
      requirePhase(getStatsPrefix(theory) + "::requirePhase", 0),
      restartDemands(getStatsPrefix(theory) + "::restartDemands", 0),
      trustedConflicts(getStatsPrefix(theory) + "::trustedConflicts", 0),
      trustedLemmas(getStatsPrefix(theory) + "::trustedLemmas", 0)
{
  smtStatisticsRegistry()->registerStat(&conflicts);
  smtStatisticsRegistry()->registerStat(&propagations);
  smtStatisticsRegistry()->registerStat(&lemmas);
  smtStatisticsRegistry()->registerStat(&requirePhase);
  smtStatisticsRegistry()->registerStat(&restartDemands);
  smtStatisticsRegistry()->registerStat(&trustedConflicts);
  smtStatisticsRegistry()->registerStat(&trustedLemmas);
}

EngineOutputChannel::Statistics::~Statistics()
{
  smtStatisticsRegistry()->unregisterStat(&conflicts);
  smtStatisticsRegistry()->unregisterStat(&propagations);
  smtStatisticsRegistry()->unregisterStat(&lemmas);
  smtStatisticsRegistry()->unregisterStat(&requirePhase);
  smtStatisticsRegistry()->unregisterStat(&restartDemands);
  smtStatisticsRegistry()->unregisterStat(&trustedConflicts);
  smtStatisticsRegistry()->unregisterStat(&trustedLemmas);
}

EngineOutputChannel::EngineOutputChannel(TheoryEngine* engine,
                                         theory::TheoryId theory)
    : d_engine(engine), d_statistics(theory), d_theory(theory)
{
}

void EngineOutputChannel::safePoint(ResourceManager::Resource r)
{
  spendResource(r);
  if (d_engine->d_interrupted)
  {
    throw theory::Interrupted();
  }
}

theory::LemmaStatus EngineOutputChannel::lemma(TNode lemma,
                                               ProofRule rule,
                                               bool removable,
                                               bool preprocess,
                                               bool sendAtoms)
{
  Debug("theory::lemma") << "EngineOutputChannel<" << d_theory << ">::lemma("
                         << lemma << ")"
                         << ", preprocess = " << preprocess << std::endl;
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;

  PROOF({ registerLemmaRecipe(lemma, lemma, preprocess, d_theory); });

  TrustNode tlem = TrustNode::mkTrustLemma(lemma);
  theory::LemmaStatus result =
      d_engine->lemma(tlem.getNode(),
                      rule,
                      false,
                      removable,
                      preprocess,
                      sendAtoms ? d_theory : theory::THEORY_LAST);
  return result;
}

void EngineOutputChannel::registerLemmaRecipe(Node lemma,
                                              Node originalLemma,
                                              bool preprocess,
                                              theory::TheoryId theoryId)
{
  // During CNF conversion, conjunctions will be broken down into
  // multiple lemmas. In order for the recipes to match, we have to do
  // the same here.
  NodeManager* nm = NodeManager::currentNM();

  if (preprocess) lemma = d_engine->preprocess(lemma);

  bool negated = (lemma.getKind() == NOT);
  Node nnLemma = negated ? lemma[0] : lemma;

  switch (nnLemma.getKind())
  {
    case AND:
      if (!negated)
      {
        for (unsigned i = 0; i < nnLemma.getNumChildren(); ++i)
          registerLemmaRecipe(nnLemma[i], originalLemma, false, theoryId);
      }
      else
      {
        NodeBuilder<> builder(OR);
        for (unsigned i = 0; i < nnLemma.getNumChildren(); ++i)
          builder << nnLemma[i].negate();

        Node disjunction =
            (builder.getNumChildren() == 1) ? builder[0] : builder;
        registerLemmaRecipe(disjunction, originalLemma, false, theoryId);
      }
      break;

    case EQUAL:
      if (nnLemma[0].getType().isBoolean())
      {
        if (!negated)
        {
          registerLemmaRecipe(nm->mkNode(OR, nnLemma[0], nnLemma[1].negate()),
                              originalLemma,
                              false,
                              theoryId);
          registerLemmaRecipe(nm->mkNode(OR, nnLemma[0].negate(), nnLemma[1]),
                              originalLemma,
                              false,
                              theoryId);
        }
        else
        {
          registerLemmaRecipe(nm->mkNode(OR, nnLemma[0], nnLemma[1]),
                              originalLemma,
                              false,
                              theoryId);
          registerLemmaRecipe(
              nm->mkNode(OR, nnLemma[0].negate(), nnLemma[1].negate()),
              originalLemma,
              false,
              theoryId);
        }
      }
      break;

    case ITE:
      if (!negated)
      {
        registerLemmaRecipe(nm->mkNode(OR, nnLemma[0].negate(), nnLemma[1]),
                            originalLemma,
                            false,
                            theoryId);
        registerLemmaRecipe(nm->mkNode(OR, nnLemma[0], nnLemma[2]),
                            originalLemma,
                            false,
                            theoryId);
      }
      else
      {
        registerLemmaRecipe(
            nm->mkNode(OR, nnLemma[0].negate(), nnLemma[1].negate()),
            originalLemma,
            false,
            theoryId);
        registerLemmaRecipe(nm->mkNode(OR, nnLemma[0], nnLemma[2].negate()),
                            originalLemma,
                            false,
                            theoryId);
      }
      break;

    default: break;
  }

  // Theory lemmas have one step that proves the empty clause
  LemmaProofRecipe proofRecipe;
  Node emptyNode;
  LemmaProofRecipe::ProofStep proofStep(theoryId, emptyNode);

  // Remember the original lemma, so we can report this later when asked to
  proofRecipe.setOriginalLemma(originalLemma);

  // Record the assertions and rewrites
  Node rewritten;
  if (lemma.getKind() == OR)
  {
    for (unsigned i = 0; i < lemma.getNumChildren(); ++i)
    {
      rewritten = theory::Rewriter::rewrite(lemma[i]);
      if (rewritten != lemma[i])
      {
        proofRecipe.addRewriteRule(lemma[i].negate(), rewritten.negate());
      }
      proofStep.addAssertion(lemma[i]);
      proofRecipe.addBaseAssertion(rewritten);
    }
  }
  else
  {
    rewritten = theory::Rewriter::rewrite(lemma);
    if (rewritten != lemma)
    {
      proofRecipe.addRewriteRule(lemma.negate(), rewritten.negate());
    }
    proofStep.addAssertion(lemma);
    proofRecipe.addBaseAssertion(rewritten);
  }
  proofRecipe.addStep(proofStep);
  ProofManager::getCnfProof()->setProofRecipe(&proofRecipe);
}

theory::LemmaStatus EngineOutputChannel::splitLemma(TNode lemma, bool removable)
{
  Debug("theory::lemma") << "EngineOutputChannel<" << d_theory << ">::lemma("
                         << lemma << ")" << std::endl;
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;

  Debug("pf::explain") << "EngineOutputChannel::splitLemma( " << lemma << " )"
                       << std::endl;
  TrustNode tlem = TrustNode::mkTrustLemma(lemma);
  theory::LemmaStatus result = d_engine->lemma(
      tlem.getNode(), RULE_SPLIT, false, removable, false, d_theory);
  return result;
}

bool EngineOutputChannel::propagate(TNode literal)
{
  Debug("theory::propagate") << "EngineOutputChannel<" << d_theory
                             << ">::propagate(" << literal << ")" << std::endl;
  ++d_statistics.propagations;
  d_engine->d_outputChannelUsed = true;
  return d_engine->propagate(literal, d_theory);
}

void EngineOutputChannel::conflict(TNode conflictNode,
                                   std::unique_ptr<Proof> proof)
{
  Trace("theory::conflict")
      << "EngineOutputChannel<" << d_theory << ">::conflict(" << conflictNode
      << ")" << std::endl;
  Assert(!proof);  // Theory shouldn't be producing proofs yet
  ++d_statistics.conflicts;
  d_engine->d_outputChannelUsed = true;
  TrustNode tConf = TrustNode::mkTrustConflict(conflictNode);
  d_engine->conflict(tConf.getNode(), d_theory);
}

void EngineOutputChannel::demandRestart()
{
  NodeManager* curr = NodeManager::currentNM();
  Node restartVar = curr->mkSkolem(
      "restartVar",
      curr->booleanType(),
      "A boolean variable asserted to be true to force a restart");
  Trace("theory::restart") << "EngineOutputChannel<" << d_theory
                           << ">::restart(" << restartVar << ")" << std::endl;
  ++d_statistics.restartDemands;
  lemma(restartVar, RULE_INVALID, true);
}

void EngineOutputChannel::requirePhase(TNode n, bool phase)
{
  Debug("theory") << "EngineOutputChannel::requirePhase(" << n << ", " << phase
                  << ")" << std::endl;
  ++d_statistics.requirePhase;
  d_engine->getPropEngine()->requirePhase(n, phase);
}

void EngineOutputChannel::setIncomplete()
{
  Trace("theory") << "setIncomplete()" << std::endl;
  d_engine->setIncomplete(d_theory);
}

void EngineOutputChannel::spendResource(ResourceManager::Resource r)
{
  d_engine->spendResource(r);
}

void EngineOutputChannel::handleUserAttribute(const char* attr,
                                              theory::Theory* t)
{
  d_engine->handleUserAttribute(attr, t);
}

void EngineOutputChannel::trustedConflict(TrustNode pconf)
{
  Assert(pconf.getKind() == TrustNodeKind::CONFLICT);
  Trace("theory::conflict")
      << "EngineOutputChannel<" << d_theory << ">::conflict(" << pconf.getNode()
      << ")" << std::endl;
  if (pconf.getGenerator() != nullptr)
  {
    ++d_statistics.trustedConflicts;
  }
  ++d_statistics.conflicts;
  d_engine->d_outputChannelUsed = true;
  d_engine->conflict(pconf.getNode(), d_theory);
}

LemmaStatus EngineOutputChannel::trustedLemma(TrustNode plem,
                                              bool removable,
                                              bool preprocess,
                                              bool sendAtoms)
{
  Assert(plem.getKind() == TrustNodeKind::LEMMA);
  if (plem.getGenerator() != nullptr)
  {
    ++d_statistics.trustedLemmas;
  }
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;
  // now, call the normal interface for lemma
  return d_engine->lemma(plem.getNode(),
                         RULE_INVALID,
                         false,
                         removable,
                         preprocess,
                         sendAtoms ? d_theory : theory::THEORY_LAST);
}

}  // namespace theory
}  // namespace CVC4
