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

#include "options/smt_options.h"
#include "smt/env.h"
#include "theory/relevance_manager.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {

DifficultyManager::DifficultyManager(RelevanceManager* rlv,
                                     context::Context* c,
                                     Valuation val)
    : d_rlv(rlv), d_input(c), d_val(val), d_dfmap(c)
{
}

void DifficultyManager::notifyInputAssertions(
    const std::vector<Node>& assertions)
{
  for (const Node& a : assertions)
  {
    d_input.insert(a);
  }
}

void DifficultyManager::getDifficultyMap(std::map<Node, Node>& dmap)
{
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const Node, uint64_t> p : d_dfmap)
  {
    dmap[p.first] = nm->mkConstInt(Rational(p.second));
  }
}

void DifficultyManager::notifyLemma(Node n, bool inFullEffortCheck)
{
  // compute if we should consider the lemma
  bool considerLemma = false;
  if (options::difficultyMode() == options::DifficultyMode::LEMMA_LITERAL_ALL)
  {
    considerLemma = true;
  }
  else if (options::difficultyMode() == options::DifficultyMode::LEMMA_LITERAL)
  {
    considerLemma = inFullEffortCheck;
  }
  if (!considerLemma)
  {
    return;
  }
  Trace("diff-man") << "notifyLemma: " << n << std::endl;
  Kind nk = n.getKind();
  // for lemma (or a_1 ... a_n), if a_i is a literal that is not true in the
  // valuation, then we increment the difficulty of that assertion
  std::vector<TNode> litsToCheck;
  if (nk == kind::OR)
  {
    litsToCheck.insert(litsToCheck.end(), n.begin(), n.end());
  }
  else if (nk == kind::IMPLIES)
  {
    litsToCheck.push_back(n[0].negate());
    litsToCheck.push_back(n[1]);
  }
  else
  {
    litsToCheck.push_back(n);
  }
  for (TNode nc : litsToCheck)
  {
    bool pol = nc.getKind() != kind::NOT;
    TNode atom = pol ? nc : nc[0];
    TNode exp = d_rlv->getExplanationForRelevant(atom);
    Trace("diff-man-debug")
        << "Check literal: " << atom << ", has reason = " << (!exp.isNull())
        << std::endl;
    // must be an input assertion
    if (!exp.isNull() && d_input.find(exp) != d_input.end())
    {
      incrementDifficulty(exp);
    }
  }
}

void DifficultyManager::notifyCandidateModel(TheoryModel* m)
{
  if (options::difficultyMode() != options::DifficultyMode::MODEL_CHECK)
  {
    return;
  }
  Trace("diff-man") << "DifficultyManager::notifyCandidateModel, #input="
                    << d_input.size() << std::endl;
  for (const Node& a : d_input)
  {
    // should have miniscoped the assertions upstream
    Assert(a.getKind() != kind::AND);
    // check if each input is satisfied
    Node av = m->getValue(a);
    if (av.isConst() && av.getConst<bool>())
    {
      continue;
    }
    Trace("diff-man") << "  not true: " << a << std::endl;
    // not satisfied, increment counter
    incrementDifficulty(a);
  }
  Trace("diff-man") << std::endl;
}
void DifficultyManager::incrementDifficulty(TNode a, uint64_t amount)
{
  Assert(a.getType().isBoolean());
  d_dfmap[a] = d_dfmap[a] + amount;
}

}  // namespace theory
}  // namespace cvc5
