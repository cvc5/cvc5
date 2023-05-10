/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Tim King, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "theory/theory_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

EngineOutputChannel::Statistics::Statistics(StatisticsRegistry& sr,
                                            const std::string& statPrefix)
    : conflicts(sr.registerInt(statPrefix + "conflicts")),
      propagations(sr.registerInt(statPrefix + "propagations")),
      lemmas(sr.registerInt(statPrefix + "lemmas")),
      requirePhase(sr.registerInt(statPrefix + "requirePhase")),
      trustedConflicts(sr.registerInt(statPrefix + "trustedConflicts")),
      trustedLemmas(sr.registerInt(statPrefix + "trustedLemmas"))
{
}

EngineOutputChannel::EngineOutputChannel(StatisticsRegistry& sr,
                                         TheoryEngine* engine,
                                         theory::TheoryId theory)
    : d_engine(engine),
      d_name(toString(theory)),
      d_statistics(sr, getStatsPrefix(theory)),
      d_theory(theory)
{
}

EngineOutputChannel::EngineOutputChannel(StatisticsRegistry& sr,
                                         TheoryEngine* engine,
                                         const std::string& name)
    : d_engine(engine),
      d_name(name),
      d_statistics(sr, name + "::"),
      d_theory(THEORY_NONE)
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
  trustedLemma(TrustNode::mkTrustLemma(lemma), p);
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

void EngineOutputChannel::requirePhase(TNode n, bool phase)
{
  Trace("theory") << "EngineOutputChannel::requirePhase(" << n << ", " << phase
                  << ")" << std::endl;
  ++d_statistics.requirePhase;
  d_engine->getPropEngine()->requirePhase(n, phase);
}

void EngineOutputChannel::setModelUnsound(IncompleteId id)
{
  Trace("theory") << "setModelUnsound(" << id << ")" << std::endl;
  d_engine->setModelUnsound(d_theory, id);
}

void EngineOutputChannel::setRefutationUnsound(IncompleteId id)
{
  Trace("theory") << "setRefutationUnsound(" << id << ")" << std::endl;
  d_engine->setRefutationUnsound(d_theory, id);
}

void EngineOutputChannel::spendResource(Resource r)
{
  d_engine->spendResource(r);
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
  if (isLemmaPropertySendAtoms(p))
  {
    d_engine->ensureLemmaAtoms(plem.getNode(), d_theory);
  }
  // now, call the normal interface for lemma
  d_engine->lemma(plem,
                  p,
                  d_theory);
}

}  // namespace theory
}  // namespace cvc5::internal
