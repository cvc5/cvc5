/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for quantifiers inference manager.
 */

#include "theory/quantifiers/quantifiers_inference_manager.h"

#include "options/base_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/skolemize.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

QuantifiersInferenceManager::QuantifiersInferenceManager(
    Env& env,
    Theory& t,
    QuantifiersState& state,
    QuantifiersRegistry& qr,
    TermRegistry& tr)
    : InferenceManagerBuffered(env, t, state, "theory::quantifiers::"),
      d_instantiate(new Instantiate(env, state, *this, qr, tr)),
      d_skolemize(new Skolemize(env, state, tr)),
      d_debugQm(nullptr),
      d_debugNumPendingLemmas(0),
      d_debugTimeStamp()
{
}

QuantifiersInferenceManager::~QuantifiersInferenceManager() {}

Instantiate* QuantifiersInferenceManager::getInstantiate()
{
  return d_instantiate.get();
}

Skolemize* QuantifiersInferenceManager::getSkolemize()
{
  return d_skolemize.get();
}

void QuantifiersInferenceManager::doPending()
{
  doPendingLemmas();
  doPendingPhaseRequirements();
}

void QuantifiersInferenceManager::beginCallDebug(QuantifiersModule* qm)
{
  bool traceOn = TraceIsOn("inst-strategy");
  if (!isOutputOn(OutputTag::INST_STRATEGY) && !traceOn)
  {
    return;
  }
  Assert(d_debugQm == nullptr);
  d_debugQm = qm;
  d_debugNumPendingLemmas = numPendingLemmas();
  d_debugTimeStamp = clock();
  if (traceOn)
  {
    Trace("inst-strategy") << "--- Run instantiation via " << qm->identify()
                           << std::endl;
  }
}

void QuantifiersInferenceManager::endCallDebug()
{
  if (d_debugQm == nullptr)
  {
    // trace and output is not enabled
    return;
  }
  Assert(numPendingLemmas() >= d_debugNumPendingLemmas);
  size_t numLemmas = numPendingLemmas() - d_debugNumPendingLemmas;
  clock_t endTimeStamp = clock() - d_debugTimeStamp;
  double time =
      static_cast<double>(endTimeStamp) / static_cast<double>(CLOCKS_PER_SEC);
  bool isConflict = d_theoryState.isInConflict();
  if (isOutputOn(OutputTag::INST_STRATEGY))
  {
    output(OutputTag::INST_STRATEGY)
        << "(inst-strategy " << d_debugQm->identify();
    if (numLemmas > 0)
    {
      output(OutputTag::INST_STRATEGY) << " :inst " << numLemmas;
    }
    output(OutputTag::INST_STRATEGY) << " :time " << time;
    if (isConflict)
    {
      output(OutputTag::INST_STRATEGY) << " :conflict";
    }
    output(OutputTag::INST_STRATEGY) << ")" << std::endl;
  }
  if (TraceIsOn("inst-strategy"))
  {
    Trace("inst-strategy") << "Finished " << d_debugQm->identify();
    if (numLemmas > 0)
    {
      Trace("inst-strategy") << ", lemmas = " << numLemmas;
    }
    Trace("inst-strategy") << (isConflict ? ", CONFLICT" : "");
    Trace("inst-strategy") << ", time = " << time << std::endl;
  }
  d_debugQm = nullptr;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
