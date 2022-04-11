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
#include "smt/env.h"
#include "smt/smt_statistics_registry.h"
#include "theory/theory_engine.h"
#include "theory/trust_substitutions.h"

namespace cvc5::internal {
namespace prop {

ZeroLevelLearner::ZeroLevelLearner(Env& env, TheoryEngine* theoryEngine)
    : EnvObj(env),
      d_theoryEngine(theoryEngine),
      d_levelZeroAsserts(userContext()),
      d_ldb(userContext()),
      d_nonZeroAssert(context(), false),
      d_ppnAtoms(userContext()),
      d_ppnTerms(userContext()),
      d_ppnSyms(userContext()),
      d_assertNoLearnCount(0)
{
  // get the learned types
  d_learnedTypes.insert(modes::LearnedLitType::INPUT);
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

void ZeroLevelLearner::notifyTopLevelSubstitution(const Node& lhs,
                                                  const Node& rhs)
{
  // process as a preprocess solved learned literal.
  Node eq = lhs.eqNode(rhs);
  processLearnedLiteral(eq, modes::LearnedLitType::PREPROCESS_SOLVED);
}

void ZeroLevelLearner::notifyInputFormulas(const std::vector<Node>& assertions)
{
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode> visitedWithinAtom;
  std::unordered_set<Node> inputSymbols;
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
    processLearnedLiteral(lit, modes::LearnedLitType::PREPROCESS);
    // also get its symbols
    expr::getSymbols(atom, inputSymbols, visitedWithinAtom);
    // remember we've seen it
    d_levelZeroAsserts.insert(lit);
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
    expr::getSymbols(a, inputSymbols, visitedWithinAtom);
  }
  for (const TNode& t : visitedWithinAtom)
  {
    d_ppnTerms.insert(t);
  }
  for (const Node& s : inputSymbols)
  {
    d_ppnSyms.insert(s);
  }

  Trace("level-zero") << "Preprocess status:" << std::endl;
  Trace("level-zero") << "#Non-learned lits = " << d_ppnAtoms.size()
                      << std::endl;
  Trace("level-zero") << "#Symbols = " << d_ppnSyms.size() << std::endl;
  Trace("level-zero") << "#Subterms = " << d_ppnTerms.size() << std::endl;
  Trace("level-zero") << "#Current top level subs = "
                      << d_env.getTopLevelSubstitutions().get().size()
                      << std::endl;
  Trace("level-zero") << d_ldb.toStringDebug();
}

bool ZeroLevelLearner::notifyAsserted(TNode assertion, int32_t alevel)
{
  // check if at level zero
  if (d_nonZeroAssert.get())
  {
    // already not at level zero, skip
    d_assertNoLearnCount++;
  }
  else if (alevel != 0)
  {
    Trace("level-zero-dec") << "First non-zero: " << assertion << std::endl;
    d_nonZeroAssert = true;
    d_assertNoLearnCount++;
  }
  else if (d_levelZeroAsserts.find(assertion) == d_levelZeroAsserts.end())
  {
    // remember we've processed this
    d_levelZeroAsserts.insert(assertion);
    // process what we should do with the learned literal
    modes::LearnedLitType ltype = computeLearnedLiteralType(assertion);
    processLearnedLiteral(assertion, ltype);
    return true;
  }
  return true;
}

modes::LearnedLitType ZeroLevelLearner::computeLearnedLiteralType(
    const Node& lit)
{
  // literal was learned, determine its type
  TNode aatom = lit.getKind() == kind::NOT ? lit[0] : lit;
  bool internal = d_ppnAtoms.find(aatom) == d_ppnAtoms.end();
  modes::LearnedLitType ltype =
      internal ? modes::LearnedLitType::INTERNAL : modes::LearnedLitType::INPUT;
  // compute if solvable
  if (internal)
  {
    Subs ss;
    if (getSolved(lit, ss))
    {
      // if we solved for any variable from input, we are SOLVABLE.
      for (const Node& v : ss.d_vars)
      {
        if (d_ppnSyms.find(v) == d_ppnSyms.end())
        {
          Trace("level-zero-assert") << "...solvable due to " << v << std::endl;
          ltype = modes::LearnedLitType::SOLVABLE;
          break;
        }
      }
    }
    if (ltype != modes::LearnedLitType::SOLVABLE)
    {
      // maybe a constant prop?
      if (lit.getKind() == kind::EQUAL)
      {
        for (size_t i = 0; i < 2; i++)
        {
          if (lit[i].isConst()
              && d_ppnTerms.find(lit[1 - i]) != d_ppnTerms.end())
          {
            ltype = modes::LearnedLitType::CONSTANT_PROP;
            break;
          }
        }
      }
    }
  }
  Trace("level-zero-assert")
      << "Level zero assert: " << lit << ", type=" << ltype << std::endl;
  return ltype;
}

void ZeroLevelLearner::processLearnedLiteral(const Node& lit,
                                             modes::LearnedLitType ltype)
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
    if (ltype != modes::LearnedLitType::INPUT)
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
    modes::LearnedLitType ltype) const
{
  std::vector<Node> ret = d_ldb.getLearnedLiterals(ltype);
  if (TraceIsOn("level-zero"))
  {
    if (!ret.empty())
    {
      Trace("level-zero") << "...learned #literals (" << ltype
                          << ") = " << ret.size() << std::endl;
    }
  }
  return ret;
}

bool ZeroLevelLearner::isLearnable(modes::LearnedLitType ltype) const
{
  return d_learnedTypes.find(ltype) != d_learnedTypes.end();
}

bool ZeroLevelLearner::getSolved(const Node& lit, Subs& subs)
{
  theory::TrustSubstitutionMap subsOut(&d_dummyContext);
  TrustNode tlit = TrustNode::mkTrustLemma(lit);
  theory::Theory::PPAssertStatus status = d_theoryEngine->solve(tlit, subsOut);
  if (status == theory::Theory::PP_ASSERT_STATUS_SOLVED)
  {
    Trace("level-zero-debug") << lit << " is solvable" << std::endl;
    // extract the substitution
    std::unordered_map<Node, Node> ss = subsOut.get().getSubstitutions();
    for (const std::pair<const Node, Node>& s : ss)
    {
      subs.add(s.first, s.second);
      Trace("level-zero-debug")
          << "  subs: " << s.first << " -> " << s.second << std::endl;
    }
    return true;
  }
  Trace("level-zero-debug") << lit << " is not solvable" << std::endl;
  return false;
}

}  // namespace prop
}  // namespace cvc5::internal
