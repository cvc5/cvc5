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
#include "theory/theory_engine.h"
#include "theory/trust_substitutions.h"

namespace cvc5 {
namespace prop {

ZeroLevelLearner::ZeroLevelLearner(Env& env,
                                   PropEngine* propEngine,
                                   TheoryEngine* theoryEngine)
    : EnvObj(env),
      d_propEngine(propEngine),
      d_theoryEngine(theoryEngine),
      d_levelZeroAsserts(userContext()),
      d_ldb(userContext()),
      d_nonZeroAssert(context(), false),
      d_ppnAtoms(userContext()),
      d_ppnSyms(userContext()),
      d_assertNoLearnCount(0)
{
}

ZeroLevelLearner::~ZeroLevelLearner() {}

void ZeroLevelLearner::getAtoms(TNode a,
                                std::unordered_set<TNode>& visited,
                                std::unordered_set<Node>& atoms)
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
      atoms.insert(cur);
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
    // we mark that we visited this
    visited.insert(atom);
    // output learned literals from preprocessing
    processLearnedLiteral(lit, LearnedLitType::PREPROCESS);
  }
  // Compute the set of literals in the preprocessed assertions
  std::unordered_set<Node> inputAtoms;
  for (const Node& a : assertions)
  {
    getAtoms(a, visited, inputAtoms);
  }
  for (const Node& a : inputAtoms)
  {
    d_ppnAtoms.insert(a);
    // also get its symbols
  }

  Trace("level-zero") << "Preprocess status:" << std::endl;
  Trace("level-zero") << "#Non-learned lits = " << d_ppnAtoms.size()
                      << std::endl;
  Trace("level-zero") << d_ldb.toStringDebug();
  Trace("level-zero") << "#Top level subs = "
                      << d_env.getTopLevelSubstitutions().get().size()
                      << std::endl;
  // the threshold is by default d_ppnAtoms.size()*3.0, which means we restart
  // if we have learned any literals, and the number of assertions since the
  // last learned literal is equal to the total number of literals in the
  // input problem times 3, i.e. each literal has been asserted on average 3
  // times.
  d_deepRestartThreshold = static_cast<size_t>(
      static_cast<double>(d_ppnAtoms.size()) * options().smt.deepRestartFactor);
  Trace("level-zero") << "Restart threshold is " << d_deepRestartThreshold
                      << std::endl;
}

bool ZeroLevelLearner::notifyAsserted(TNode assertion)
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
      // remember we've processed this
      d_levelZeroAsserts.insert(assertion);
      // process what we should do with the learned literal
      LearnedLitType ltype = computeLearnedLiteralType(assertion);
      processLearnedLiteral(assertion, ltype);
    }
    else
    {
      d_nonZeroAssert = true;
    }
    d_assertNoLearnCount++;
  }
  if (TraceIsOn("level-zero-assert"))
  {
    if (d_assertNoLearnCount % 1000 == 0)
    {
      Trace("level-zero-assert")
          << "#asserts without learning = " << d_assertNoLearnCount
          << " (#atoms is " << d_ppnAtoms.size()
          << ", #learned = " << d_ldb.getNumLearnedLiterals() << ")"
          << std::endl;
    }
  }
  // request a deep restart?
  if (options().smt.deepRestart)
  {
    if (d_ldb.getNumLearnedLiterals() > 0)
    {
      // if non-empty and non-learned atoms have been asserted beyond the
      // threshold
      if (d_assertNoLearnCount > d_deepRestartThreshold)
      {
        Trace("level-zero")
            << "DEEP RESTART with " << d_ldb.getNumLearnedLiterals()
            << " learned literals" << std::endl;
        return false;
      }
    }
  }
  return true;
}

LearnedLitType ZeroLevelLearner::computeLearnedLiteralType(
    const Node& lit) const
{
  // literal was learned, determine its type
  TNode aatom = lit.getKind() == kind::NOT ? lit[0] : lit;
  bool internal = d_ppnAtoms.find(aatom) == d_ppnAtoms.end();
  LearnedLitType ltype =
      internal ? LearnedLitType::INTERNAL : LearnedLitType::INPUT;
  // compute if solvable
  Trace("level-zero-assert")
      << "Level zero assert: " << lit << ", type=" << ltype << std::endl;
  return ltype;
}

void ZeroLevelLearner::processLearnedLiteral(const Node& lit,
                                             LearnedLitType ltype)
{
  // add to the database
  d_ldb.addLearnedLiteral(lit, ltype);
  // reset the counter for deep restart if the literal was learnable
  if (isLearnable(ltype))
  {
    d_assertNoLearnCount = 0;
  }
  // print to stream
  if (isOutputOn(OutputTag::LEARNED_LITS))
  {
    // get the original form so that internally generated variables
    // are mapped back to their original form
    output(OutputTag::LEARNED_LITS)
        << "(learned-lit " << SkolemManager::getOriginalForm(lit);
    if (ltype != LearnedLitType::INPUT)
    {
      std::stringstream tss;
      tss << ltype;
      std::string ltstr = tss.str();
      std::transform(
          ltstr.begin(), ltstr.end(), ltstr.begin(), [](unsigned char c) {
            return std::tolower(c);
          });
      output(OutputTag::LEARNED_LITS) << " :" << ltstr;
    }
    output(OutputTag::LEARNED_LITS) << ")" << std::endl;
  }
}

std::vector<Node> ZeroLevelLearner::getLearnedZeroLevelLiterals(
    LearnedLitType ltype) const
{
  std::vector<Node> ret = d_ldb.getLearnedLiterals(ltype);
  Trace("level-zero") << "Get zero level learned " << ltype << " " << ret.size()
                      << std::endl;
  return ret;
}

bool ZeroLevelLearner::isLearnable(LearnedLitType ltype) const
{
  if (ltype == LearnedLitType::INPUT)
  {
    return true;
  }
  options::DeepRestartLearnMode lmode = options().smt.deepRestartLearnMode;
  if (ltype == LearnedLitType::INTERNAL)
  {
    return lmode == options::DeepRestartLearnMode::ALL;
  }
  else if (ltype == LearnedLitType::SOLVABLE)
  {
    return lmode == options::DeepRestartLearnMode::ALL
           || lmode == options::DeepRestartLearnMode::INPUT_AND_SOLVABLE;
  }
  return false;
}

}  // namespace prop
}  // namespace cvc5
