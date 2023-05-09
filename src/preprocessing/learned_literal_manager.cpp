/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Learned literal manager
 */

#include "preprocessing/learned_literal_manager.h"

#include "smt/env.h"
#include "theory/rewriter.h"
#include "theory/trust_substitutions.h"

namespace cvc5::internal {
namespace preprocessing {

LearnedLiteralManager::LearnedLiteralManager(Env& env)
    : EnvObj(env), d_learnedLits(userContext())
{
}

void LearnedLiteralManager::notifyLearnedLiteral(TNode lit)
{
  d_learnedLits.insert(lit);
  Trace("pp-llm") << "LLM:notifyLearnedLiteral: " << lit << std::endl;
}

std::vector<Node> LearnedLiteralManager::getLearnedLiterals() const
{
  theory::TrustSubstitutionMap& tls = d_env.getTopLevelSubstitutions();
  std::vector<Node> currLearnedLits;
  for (const auto& lit: d_learnedLits)
  {
    // update based on substitutions
    Node tlsNode = tls.get().apply(lit);
    tlsNode = rewrite(tlsNode);
    currLearnedLits.push_back(tlsNode);
    Trace("pp-llm") << "Learned literal : " << tlsNode << " from " << lit
                    << std::endl;
  }
  return currLearnedLits;
}

}  // namespace preprocessing
}  // namespace cvc5::internal
