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

theory::LemmaStatus EngineOutputChannel::lemma(TNode lemma, LemmaProperty p)
{
  Debug("theory::lemma") << "EngineOutputChannel<" << d_theory << ">::lemma("
                         << lemma << ")"
                         << ", properties = " << p << std::endl;
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;

  TrustNode tlem = TrustNode::mkTrustLemma(lemma);
  theory::LemmaStatus result = d_engine->lemma(
      tlem.getNode(),
      false,
      p,
      isLemmaPropertySendAtoms(p) ? d_theory : theory::THEORY_LAST);
  return result;
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
  LemmaProperty p = removable ? LemmaProperty::REMOVABLE : LemmaProperty::NONE;
  theory::LemmaStatus result =
      d_engine->lemma(tlem.getNode(), false, p, d_theory);
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

void EngineOutputChannel::conflict(TNode conflictNode)
{
  Trace("theory::conflict")
      << "EngineOutputChannel<" << d_theory << ">::conflict(" << conflictNode
      << ")" << std::endl;
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
  lemma(restartVar, LemmaProperty::REMOVABLE);
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

LemmaStatus EngineOutputChannel::trustedLemma(TrustNode plem, LemmaProperty p)
{
  Assert(plem.getKind() == TrustNodeKind::LEMMA);
  if (plem.getGenerator() != nullptr)
  {
    ++d_statistics.trustedLemmas;
  }
  ++d_statistics.lemmas;
  d_engine->d_outputChannelUsed = true;
  // now, call the normal interface for lemma
  return d_engine->lemma(
      plem.getNode(),
      false,
      p,
      isLemmaPropertySendAtoms(p) ? d_theory : theory::THEORY_LAST);
}

}  // namespace theory
}  // namespace CVC4
