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
 * Learned literal manager
 */

#include "preprocessing/learned_literal_manager.h"

#include "theory/rewriter.h"

namespace cvc5 {
namespace preprocessing {

LearnedLiteralManager::LearnedLiteralManager(theory::TrustSubstitutionMap& tls,
                                             context::UserContext* u,
                                             ProofNodeManager* pnm)
    : d_topLevelSubs(tls), d_learnedLits(u)
{
}

void LearnedLiteralManager::notifyLearnedLiteral(TNode lit)
{
  d_learnedLits.insert(lit);
  Trace("pp-llm") << "LLM:notifyLearnedLiteral: " << lit << std::endl;
}

std::vector<Node> LearnedLiteralManager::getLearnedLiterals() const
{
  std::vector<Node> currLearnedLits;
  for (const auto& lit: d_learnedLits)
  {
    // update based on substitutions
    Node tlsNode = d_topLevelSubs.get().apply(lit);
    tlsNode = theory::Rewriter::rewrite(tlsNode);
    currLearnedLits.push_back(tlsNode);
    Trace("pp-llm") << "Learned literal : " << tlsNode << " from " << lit
                    << std::endl;
  }
  return currLearnedLits;
}

}  // namespace preprocessing
}  // namespace cvc5
