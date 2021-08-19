/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Haniel Barbosa, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of module for processing proof nodes.
 */

#include "smt/difficulty_post_processor.h"

#include "smt/env.h"

using namespace cvc5::kind;
using namespace cvc5::theory;

namespace cvc5 {
namespace smt {

DifficultyPostprocessCallback::DifficultyPostprocessCallback(Env& env)
    : d_env(env), d_currDifficulty(0)
{
}
void DifficultyPostprocessCallback::setCurrentDifficulty(Node d)
{
}
bool DifficultyPostprocessCallback::shouldUpdate(std::shared_ptr<ProofNode> pn,
                                                 const std::vector<Node>& fa,
                                                 bool& continueUpdate)
{
  if (pn->getRule()==PfRule::ASSUME)
  {
    
  }
  return true;
}

}  // namespace smt
}  // namespace cvc5
