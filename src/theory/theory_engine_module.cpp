/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Amalee Wilson
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Virtual class for theory engine modules
 */

#include "theory/theory_engine_module.h"

namespace cvc5::internal {
namespace theory {

size_t TheoryEngineModule::d_idCounter = 0;
TheoryEngineModule::TheoryEngineModule(Env& env,
                                       TheoryEngine* engine,
                                       const std::string& name)
    : EnvObj(env), d_out(statisticsRegistry(), engine, name, d_idCounter)
{
  // increment the id counter so that the id of this module is unique
  d_idCounter++;
}

void TheoryEngineModule::presolve() {}

void TheoryEngineModule::postsolve(prop::SatValue result) {}

void TheoryEngineModule::check(Theory::Effort effort) {}

void TheoryEngineModule::postCheck(Theory::Effort effort) {}

void TheoryEngineModule::notifyLemma(TNode n,
                                     InferenceId id,
                                     LemmaProperty p,
                                     const std::vector<Node>& skAsserts,
                                     const std::vector<Node>& sks)
{
}

bool TheoryEngineModule::needsCandidateModel() { return false; }

void TheoryEngineModule::notifyCandidateModel(TheoryModel* m) {}

TheoryId TheoryEngineModule::getId() const { return d_out.getId(); }

}  // namespace theory
}  // namespace cvc5::internal
