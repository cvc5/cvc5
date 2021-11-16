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
#include "theory/theory_model.h"
#include "util/rational.h"

using namespace cvc5::kind;

namespace cvc5 {
namespace theory {

DifficultyManager::DifficultyManager(context::Context* c, Valuation val)
    : d_val(val), d_dfmap(c)
{
}

void DifficultyManager::getDifficultyMap(std::map<Node, Node>& dmap)
{
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const Node, uint64_t> p : d_dfmap)
  {
    dmap[p.first] = nm->mkConst(CONST_RATIONAL, Rational(p.second));
  }
}

void DifficultyManager::notifyLemma(const std::map<TNode, TNode>& rse, Node n)
{
  if (options::difficultyMode() != options::DifficultyMode::LEMMA_LITERAL)
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
  std::map<TNode, TNode>::const_iterator it;
  for (TNode nc : litsToCheck)
  {
    bool pol = nc.getKind() != kind::NOT;
    TNode atom = pol ? nc : nc[0];
    it = rse.find(atom);
    if (it != rse.end())
    {
      incrementDifficulty(it->second);
    }
  }
}

void DifficultyManager::notifyCandidateModel(const NodeList& input,
                                             TheoryModel* m)
{
  if (options::difficultyMode() != options::DifficultyMode::MODEL_CHECK)
  {
    return;
  }
  Trace("diff-man") << "DifficultyManager::notifyCandidateModel, #input="
                    << input.size() << std::endl;
  for (const Node& a : input)
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
