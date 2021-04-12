/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The theory engine output channel.
 */

#include "theory/engine_output_channel.h"

#include "expr/skolem_manager.h"
#include "prop/prop_engine.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory_engine.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {

EngineOutputChannel::Statistics::Statistics(theory::TheoryId theory)
    : conflicts(smtStatisticsRegistry().registerInt(getStatsPrefix(theory)
                                                    + "conflicts")),
      propagations(smtStatisticsRegistry().registerInt(getStatsPrefix(theory)
                                                       + "propagations")),
      lemmas(smtStatisticsRegistry().registerInt(getStatsPrefix(theory)
                                                 + "lemmas")),
      requirePhase(smtStatisticsRegistry().registerInt(getStatsPrefix(theory)
                                                       + "requirePhase")),
      restartDemands(smtStatisticsRegistry().registerInt(getStatsPrefix(theory)
                                                         + "restartDemands")),
      trustedConflicts(smtStatisticsRegistry().registerInt(
          getStatsPrefix(theory) + "trustedConflicts")),
      trustedLemmas(smtStatisticsRegistry().registerInt(getStatsPrefix(theory)
                                                        + "trustedLemmas"))
{
}

EngineOutputChannel::EngineOutputChannel(TheoryEngine* engine,
                                         theory::TheoryId theory)
    : d_engine(engine), d_statistics(theory), d_theory(theory)
{
}

void EngineOutputChannel::safePoint(Resource r)
{
  spendResource(r);
  if (d_engine->d_interrupted)
  {
    throw theory::Interrupted();
  }
}

void EngineOutputChannel::lemma(TNode lemma, LemmaProperty p)
{
  Trace("theory::lemma") << "EngineOutputChannel<" << d_theory << ">::lemma("
                         << lemma << ")"
                         << ", properties = " << p << std::endl;
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;

  TrustNode tlem = TrustNode::mkTrustLemma(lemma);
  d_engine->lemma(tlem,
                  p,
                  isLemmaPropertySendAtoms(p) ? d_theory : theory::THEORY_LAST,
                  d_theory);
}

void EngineOutputChannel::splitLemma(TNode lemma, bool removable)
{
  Trace("theory::lemma") << "EngineOutputChannel<" << d_theory << ">::lemma("
                         << lemma << ")" << std::endl;
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;

  Trace("pf::explain") << "EngineOutputChannel::splitLemma( " << lemma << " )"
                       << std::endl;
  TrustNode tlem = TrustNode::mkTrustLemma(lemma);
  LemmaProperty p = removable ? LemmaProperty::REMOVABLE : LemmaProperty::NONE;
  d_engine->lemma(tlem, p, d_theory);
}

bool EngineOutputChannel::propagate(TNode literal)
{
  Trace("theory::propagate") << "EngineOutputChannel<" << d_theory
                             << ">::propagate(" << literal << ")" << std::endl;
  ++d_statistics.propagations;
  d_engine->d_outputChannelUsed = true;
  return d_engine->propagate(literal, d_theory);
}

void EngineOutputChannel::conflict(TNode conflictNode)
{
  Trace("theory::conflict")
      << "EngineOutputChannel<" << d_theory << ">::conflict(" << conflictNode
      << ")" << std::endl;
  ++d_statistics.conflicts;
  d_engine->d_outputChannelUsed = true;
  TrustNode tConf = TrustNode::mkTrustConflict(conflictNode);
  d_engine->conflict(tConf, d_theory);
}

void EngineOutputChannel::demandRestart()
{
  NodeManager* nm = NodeManager::currentNM();
  SkolemManager* sm = nm->getSkolemManager();
  Node restartVar = sm->mkDummySkolem(
      "restartVar",
      nm->booleanType(),
      "A boolean variable asserted to be true to force a restart");
  Trace("theory::restart") << "EngineOutputChannel<" << d_theory
                           << ">::restart(" << restartVar << ")" << std::endl;
  ++d_statistics.restartDemands;
  lemma(restartVar, LemmaProperty::REMOVABLE);
}

void EngineOutputChannel::requirePhase(TNode n, bool phase)
{
  Trace("theory") << "EngineOutputChannel::requirePhase(" << n << ", " << phase
                  << ")" << std::endl;
  ++d_statistics.requirePhase;
  d_engine->getPropEngine()->requirePhase(n, phase);
}

void EngineOutputChannel::setIncomplete(IncompleteId id)
{
  Trace("theory") << "setIncomplete(" << id << ")" << std::endl;
  d_engine->setIncomplete(d_theory, id);
}

void EngineOutputChannel::spendResource(Resource r)
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
      << "EngineOutputChannel<" << d_theory << ">::trustedConflict("
      << pconf.getNode() << ")" << std::endl;
  if (pconf.getGenerator() != nullptr)
  {
    ++d_statistics.trustedConflicts;
  }
  ++d_statistics.conflicts;
  d_engine->d_outputChannelUsed = true;
  d_engine->conflict(pconf, d_theory);
}

void EngineOutputChannel::trustedLemma(TrustNode plem, LemmaProperty p)
{
  Trace("theory::lemma") << "EngineOutputChannel<" << d_theory
                         << ">::trustedLemma(" << plem << ")" << std::endl;
  Assert(plem.getKind() == TrustNodeKind::LEMMA);
  if (plem.getGenerator() != nullptr)
  {
    ++d_statistics.trustedLemmas;
  }
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;
  // now, call the normal interface for lemma
  d_engine->lemma(plem,
                  p,
                  isLemmaPropertySendAtoms(p) ? d_theory : theory::THEORY_LAST,
                  d_theory);
}

}  // namespace theory
}  // namespace cvc5
