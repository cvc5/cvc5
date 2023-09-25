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

#include "theory/output_channel.h"

#include "expr/skolem_manager.h"
#include "prop/prop_engine.h"
#include "theory/theory_engine.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

OutputChannel::Statistics::Statistics(StatisticsRegistry& sr,
                                      const std::string& statPrefix)
    : conflicts(sr.registerInt(statPrefix + "conflicts")),
      propagations(sr.registerInt(statPrefix + "propagations")),
      lemmas(sr.registerInt(statPrefix + "lemmas")),
      preferPhase(sr.registerInt(statPrefix + "preferPhase")),
      trustedConflicts(sr.registerInt(statPrefix + "trustedConflicts")),
      trustedLemmas(sr.registerInt(statPrefix + "trustedLemmas"))
{
}

OutputChannel::OutputChannel(StatisticsRegistry& sr,
                             TheoryEngine* engine,
                             theory::TheoryId theory)
    : d_engine(engine),
      d_name(toString(theory)),
      d_statistics(sr, getStatsPrefix(theory)),
      d_theory(theory)
{
}

OutputChannel::OutputChannel(StatisticsRegistry& sr,
                             TheoryEngine* engine,
                             const std::string& name,
                             size_t id)
    : d_engine(engine),
      d_name(name),
      d_statistics(sr, name + "::"),
      d_theory(static_cast<TheoryId>(THEORY_NONE + id))
{
}

void OutputChannel::safePoint(Resource r)
{
  spendResource(r);
  if (d_engine->d_interrupted)
  {
    throw theory::Interrupted();
  }
}

void OutputChannel::lemma(TNode lemma, InferenceId id, LemmaProperty p)
{
  trustedLemma(TrustNode::mkTrustLemma(lemma), id, p);
}

bool OutputChannel::propagate(TNode literal)
{
  Trace("theory::propagate") << "OutputChannel<" << d_theory << ">::propagate("
                             << literal << ")" << std::endl;
  ++d_statistics.propagations;
  d_engine->d_outputChannelUsed = true;
  return d_engine->propagate(literal, d_theory);
}

void OutputChannel::conflict(TNode conflictNode, InferenceId id)
{
  Trace("theory::conflict") << "OutputChannel<" << d_theory << ">::conflict("
                            << conflictNode << ")" << std::endl;
  ++d_statistics.conflicts;
  d_engine->d_outputChannelUsed = true;
  TrustNode tConf = TrustNode::mkTrustConflict(conflictNode);
  d_engine->conflict(tConf, id, d_theory);
}

void OutputChannel::preferPhase(TNode n, bool phase)
{
  Trace("theory") << "OutputChannel::preferPhase(" << n << ", " << phase << ")"
                  << std::endl;
  ++d_statistics.preferPhase;
  d_engine->getPropEngine()->preferPhase(n, phase);
}

void OutputChannel::setModelUnsound(IncompleteId id)
{
  Trace("theory") << "setModelUnsound(" << id << ")" << std::endl;
  d_engine->setModelUnsound(d_theory, id);
}

void OutputChannel::setRefutationUnsound(IncompleteId id)
{
  Trace("theory") << "setRefutationUnsound(" << id << ")" << std::endl;
  d_engine->setRefutationUnsound(d_theory, id);
}

void OutputChannel::spendResource(Resource r) { d_engine->spendResource(r); }

void OutputChannel::trustedConflict(TrustNode pconf, InferenceId id)
{
  Assert(pconf.getKind() == TrustNodeKind::CONFLICT);
  Trace("theory::conflict")
      << "OutputChannel<" << d_theory << ">::trustedConflict("
      << pconf.getNode() << ")" << std::endl;
  if (pconf.getGenerator() != nullptr)
  {
    ++d_statistics.trustedConflicts;
  }
  ++d_statistics.conflicts;
  d_engine->d_outputChannelUsed = true;
  d_engine->conflict(pconf, id, d_theory);
}

void OutputChannel::trustedLemma(TrustNode plem,
                                 InferenceId id,
                                 LemmaProperty p)
{
  Trace("theory::lemma") << "OutputChannel<" << d_theory << ">::trustedLemma("
                         << plem << ")" << std::endl;
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
  d_engine->lemma(plem, id, p, d_theory);
}

TheoryId OutputChannel::getId() const { return d_theory; }

}  // namespace theory
}  // namespace cvc5::internal
