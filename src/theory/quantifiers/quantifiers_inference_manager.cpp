/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for quantifiers inference manager.
 */

#include "theory/quantifiers/quantifiers_inference_manager.h"

#include "theory/quantifiers/instantiate.h"
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
      d_skolemize(new Skolemize(env, state, tr))
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

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
