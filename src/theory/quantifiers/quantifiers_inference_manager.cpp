/*********************                                                        */
/*! \file quantifiers_inference_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility for quantifiers inference manager
 **/

#include "theory/quantifiers/quantifiers_inference_manager.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

QuantifiersInferenceManager::QuantifiersInferenceManager(
    Theory& t, QuantifiersState& state, ProofNodeManager* pnm)
    : InferenceManagerBuffered(t, state, pnm)
{
}

QuantifiersInferenceManager::~QuantifiersInferenceManager() {}

void QuantifiersInferenceManager::doPending()
{
  doPendingLemmas();
  doPendingPhaseRequirements();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
