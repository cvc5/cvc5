/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Difficulty manager.
 */

#include "theory/difficulty_manager.h"

#include "expr/node_algorithm.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "theory/relevance_manager.h"
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {

DifficultyManager::DifficultyManager(Env& env,
                                     RelevanceManager* rlv,
                                     Valuation val)
    : EnvObj(env),
      d_rlv(rlv),
      d_input(userContext()),
      d_lemma(userContext()),
      d_val(val),
      d_dfmap(userContext())
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

void DifficultyManager::getDifficultyMap(std::map<Node, Node>& dmap,
                                         bool includeLemmas)
{
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const Node, uint64_t> p : d_dfmap)
  {
    if (!includeLemmas)
    {
      if (d_input.find(p.first) == d_input.end())
      {
        continue;
      }
    }
    dmap[p.first] = nm->mkConstInt(Rational(p.second));
  }
}

uint64_t DifficultyManager::getCurrentDifficulty(const Node& n) const
{
  NodeUIntMap::const_iterator it = d_dfmap.find(n);
  if (it != d_dfmap.end())
  {
    return it->second;
  }
  return 0;
}

void DifficultyManager::notifyLemma(Node n, bool inFullEffortCheck)
{
  d_lemma.insert(n);
  // compute if we should consider the lemma
  bool considerLemma = false;
  if (options().smt.difficultyMode
      == options::DifficultyMode::LEMMA_LITERAL_ALL)
  {
    considerLemma = true;
  }
  else if (options().smt.difficultyMode
           == options::DifficultyMode::LEMMA_LITERAL)
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
  std::vector<Node> litsToCheck;
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
  size_t index = 0;
  while (index < litsToCheck.size())
  {
    Node nc = litsToCheck[index];
    index++;
    if (expr::isBooleanConnective(nc))
    {
      litsToCheck.insert(litsToCheck.end(), nc.begin(), nc.end());
      continue;
    }
    TNode exp = d_rlv->getExplanationForRelevant(nc);
    Trace("diff-man-debug")
        << "Check literal: " << nc << ", has reason = " << (!exp.isNull())
        << std::endl;
    // could be input assertion or lemma
    if (!exp.isNull())
    {
      incrementDifficulty(exp);
    }
  }
}

bool DifficultyManager::needsCandidateModel() const
{
  return options().smt.difficultyMode == options::DifficultyMode::MODEL_CHECK;
}

void DifficultyManager::notifyCandidateModel(TheoryModel* m)
{
  Assert(needsCandidateModel());
  Trace("diff-man") << "DifficultyManager::notifyCandidateModel, #input="
                    << d_input.size() << " #lemma=" << d_lemma.size()
                    << std::endl;
  for (size_t i = 0; i < 2; i++)
  {
    NodeSet& ns = i == 0 ? d_input : d_lemma;
    for (const Node& a : ns)
    {
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
  }
  Trace("diff-man") << std::endl;
}
void DifficultyManager::incrementDifficulty(TNode a, uint64_t amount)
{
  Assert(a.getType().isBoolean());
  Trace("diff-man") << "incrementDifficulty: " << a << " +" << amount
                    << std::endl;
  d_dfmap[a] = d_dfmap[a] + amount;
}

}  // namespace theory
}  // namespace cvc5::internal
