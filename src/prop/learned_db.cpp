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
 * Stores learned information
 */

#include "prop/learned_db.h"

namespace cvc5 {
namespace prop {


LearnedDb::LearnedDb(context::Context * c) :
      d_levelZeroAssertsLearned(c),
      d_levelZeroInternalAssertsLearned(c)
      {}

LearnedDb::~LearnedDb() {}

void LearnedDb::addLearnedLiteral(const Node& lit, bool isInternal)
{
  if (isInternal)
  {
    d_levelZeroInternalAssertsLearned.insert(lit);
  }
  else
  {
    d_levelZeroAssertsLearned.insert(lit);
  }
}

std::vector<Node> LearnedDb::getLearnedZeroLevelLiterals(bool isInternal) const
{
  const NodeSet& la = isInternal ? d_levelZeroInternalAssertsLearned
                                 : d_levelZeroAssertsLearned;
  std::vector<Node> ret;
  for (const Node& n : la)
  {
    ret.push_back(n);
  }
  return ret;
}

}  // namespace prop
}  // namespace cvc5
