/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Learner for literals asserted at level zero.
 */
#include "prop/zero_level_learner.h"

#include "context/context.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/base_options.h"
#include "options/smt_options.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/smt_statistics_registry.h"
#include "theory/trust_substitutions.h"

namespace cvc5::internal {
namespace prop {

ZeroLevelLearner::ZeroLevelLearner(Env& env, PropEngine* propEngine)
    : EnvObj(env),
      d_propEngine(propEngine),
      d_levelZeroAsserts(userContext()),
      d_levelZeroAssertsLearned(userContext()),
      d_nonZeroAssert(context(), false),
      d_ppnAtoms(userContext()),
      d_pplAtoms(userContext()),
      d_assertNoLearnCount(0)
{
}

ZeroLevelLearner::~ZeroLevelLearner() {}

void ZeroLevelLearner::getAtoms(TNode a,
                                std::unordered_set<TNode>& visited,
                                NodeSet& ppLits)
{
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(a);
  do
  {
    cur = visit.back();
    visit.pop_back();
    if (visited.find(cur) == visited.end())
    {
      visited.insert(cur);
      if (expr::isBooleanConnective(cur))
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
        continue;
      }
      ppLits.insert(cur);
    }
  } while (!visit.empty());
}

void ZeroLevelLearner::notifyInputFormulas(
    const std::vector<Node>& assertions,
    const std::unordered_map<size_t, Node>& skolemMap)
{
  d_assertNoLearnCount = 0;
  std::unordered_set<TNode> visited;
  // We consider top level literals of assertions, including those occurring
  // as children of AND to be the preprocessed learned literals only, and not
  // the literals tracked by the preprocessor
  // (Preprocessor::getLearnedLiterals). This means that a learned literal from
  // e.g. circuit propagation that is not trivially a top level assertion will
  // be considered an ordinary learned literal.
  // Note that d_pplAtoms and d_ppnAtoms are disjoint
  std::vector<Node> toProcess = assertions;
  size_t index = 0;
  while (index < toProcess.size())
  {
    TNode lit = toProcess[index];
    index++;
    if (lit.getKind() == kind::AND)
    {
      toProcess.insert(toProcess.end(), lit.begin(), lit.end());
      continue;
    }
    TNode atom = lit.getKind() == kind::NOT ? lit[0] : lit;
    if (expr::isBooleanConnective(atom))
    {
      continue;
    }
    visited.insert(atom);
    d_pplAtoms.insert(atom);
  }
  if (isOutputOn(OutputTag::LEARNED_LITS))
  {
    // output learned literals from preprocessing
    for (const Node& lit : d_pplAtoms)
    {
      output(OutputTag::LEARNED_LITS)
          << "(learned-lit " << SkolemManager::getOriginalForm(lit)
          << " :preprocess)" << std::endl;
    }
  }
  // Compute the set of literals in the preprocessed assertions
  for (const Node& a : assertions)
  {
    getAtoms(a, visited, d_ppnAtoms);
  }

  Trace("level-zero") << "Preprocess status:" << std::endl;
  Trace("level-zero") << "#Non-learned lits = " << d_ppnAtoms.size()
                      << std::endl;
  Trace("level-zero") << "#Learned lits = " << d_pplAtoms.size() << std::endl;
  Trace("level-zero") << "#Top level subs = "
                      << d_env.getTopLevelSubstitutions().get().size()
                      << std::endl;
}

void ZeroLevelLearner::notifyAsserted(TNode assertion)
{
  // check if at level zero
  if (d_nonZeroAssert.get())
  {
    d_assertNoLearnCount++;
  }
  else if (d_levelZeroAsserts.find(assertion) == d_levelZeroAsserts.end())
  {
    int32_t alevel = d_propEngine->getDecisionLevel(assertion);
    if (alevel == 0)
    {
      TNode aatom = assertion.getKind() == kind::NOT ? assertion[0] : assertion;
      bool learnable = d_ppnAtoms.find(aatom) != d_ppnAtoms.end();
      Trace("level-zero-assert")
          << "Level zero assert: " << assertion << ", learnable=" << learnable
          << ", already learned="
          << (d_pplAtoms.find(aatom) != d_pplAtoms.end()) << std::endl;
      d_levelZeroAsserts.insert(assertion);
      if (learnable)
      {
        d_assertNoLearnCount = 0;
        d_levelZeroAssertsLearned.insert(assertion);
        Trace("level-zero-assert")
            << "#learned now " << d_levelZeroAssertsLearned.size() << std::endl;
        if (isOutputOn(OutputTag::LEARNED_LITS))
        {
          // get the original form so that internally generated variables
          // are mapped back to their original form
          output(OutputTag::LEARNED_LITS)
              << "(learned-lit " << SkolemManager::getOriginalForm(assertion)
              << ")" << std::endl;
        }
        return;
      }
    }
    else
    {
      d_nonZeroAssert = true;
    }
    d_assertNoLearnCount++;
  }
}

std::vector<Node> ZeroLevelLearner::getLearnedZeroLevelLiterals() const
{
  std::vector<Node> ret;
  for (const Node& n : d_levelZeroAssertsLearned)
  {
    ret.push_back(n);
  }
  return ret;
}

}  // namespace prop
}  // namespace cvc5::internal
