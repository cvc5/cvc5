/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
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

namespace cvc5 {
namespace theory {
namespace quantifiers {

QuantifiersInferenceManager::QuantifiersInferenceManager(
    Theory& t,
    QuantifiersState& state,
    QuantifiersRegistry& qr,
    TermRegistry& tr,
    ProofNodeManager* pnm)
    : InferenceManagerBuffered(t, state, pnm, "theory::quantifiers::"),
      d_instantiate(new Instantiate(state, *this, qr, tr, pnm)),
      d_skolemize(new Skolemize(state, tr, pnm))
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
}  // namespace cvc5
