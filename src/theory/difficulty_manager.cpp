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
#include "theory/theory_model.h"
#include "util/rational.h"

namespace cvc5 {
namespace theory {

DifficultyManager::DifficultyManager(Env& env) : d_dfmap(env.getUserContext())
{
}

void DifficultyManager::getDifficultyMap(std::map<Node, Node>& dmap)
{
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const Node, uint64_t>& p : d_dfmap)
  {
    dmap[p.first] = nm->mkConst(Rational(p.second));
  }
}

void DifficultyManager::notifyCandidateModel(const NodeList& input,
                                             TheoryModel* m)
{
  Trace("diff-man") << "DifficultyManager::notifyCandidateModel, #input=" << input.size() << std::endl;
  for (const Node& a : input)
  {
    // check if each input is satisfied
    Node av = m->getValue(a);
    if (av.isConst() && av.getConst<bool>())
    {
      continue;
    }
    Trace("diff-man") << "  not true: " << a << std::endl;
    // not satisfied, increment counter
    d_dfmap[a] = d_dfmap[a] + 1;
  }
  Trace("diff-man") << std::endl;
}

}  // namespace theory
}  // namespace cvc5
