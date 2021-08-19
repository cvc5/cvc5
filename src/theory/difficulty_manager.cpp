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
 * Difficulty manager.
 */

#include "theory/difficulty_manager.h"

#include "smt/env.h"

namespace cvc5 {
namespace theory {

DifficultyManager::DifficultyManager(Env& env) : d_dfmap(env.getUserContext())
{
}

void DifficultyManager::getDifficultyMap(std::map<Node, Node>& dmap) {}

void DifficultyManager::notifyCandidateModel(const NodeList& input,
                                             TheoryModel* m)
{
}

}  // namespace theory
}  // namespace cvc5
