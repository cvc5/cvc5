/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A module for computing a timeout core from a set of assertions.
 */

#include "smt/timeout_core_manager.h"

#include <cvc5/cvc5_types.h>

#include <fstream>

#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/smt_options.h"
#include "printer/printer.h"
#include "proof/proof_node_algorithm.h"
#include "prop/prop_engine.h"
#include "smt/env.h"
#include "smt/print_benchmark.h"
#include "smt/smt_solver.h"
#include "smt/solver_engine.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/substitutions.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "util/random.h"

namespace cvc5::internal {
namespace smt {

TimeoutCoreManager::TimeoutCoreManager(Env& env)
    : EnvObj(env), d_numAssertsNsk(0)
{
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
}

std::pair<Result, std::vector<Node>> TimeoutCoreManager::getTimeoutCore(
    const std::vector<Node>& ppAsserts,
    const std::map<size_t, Node>& ppSkolemMap,
    const std::vector<Node>& assumptions)
{
  d_ppAsserts.clear();
  d_ppAssertsOrig.clear();
  d_skolemToAssert.clear();
  d_modelValues.clear();
  d_modelToAssert.clear();
  d_unkModels.clear();
  d_ainfo.clear();
  d_asymbols.clear();
  d_syms.clear();
  d_globalInclude.clear();
  initializeAssertions(ppAsserts, ppSkolemMap, assumptions);

  std::vector<size_t> nextInclude;
  Result result;
  bool checkAgain = true;
  do
  {
    std::vector<Node> assertions;
    // get the next assertions, store in d_ap
    getNextAssertions(nextInclude, assertions);
    nextInclude.clear();
    // check sat based on the driver strategy
    result = checkSatNext(assertions, nextInclude);
    // if we were asked to check again
    if (result.getStatus() != Result::UNKNOWN
        || result.getUnknownExplanation()
               != UnknownExplanation::REQUIRES_CHECK_AGAIN)
    {
      checkAgain = false;
    }
  } while (checkAgain);

  std::vector<Node> toCore;
  for (std::pair<const size_t, AssertInfo>& a : d_ainfo)
  {
    Assert(a.first < d_ppAssertsOrig.size());
    toCore.push_back(d_ppAssertsOrig[a.first]);
  }
  // include the skolem definitions
  if (assumptions.empty())
  {
    getActiveDefinitions(toCore);
  }
  if (TraceIsOn("to-core-result"))
  {
    for (const Node& c : toCore)
    {
      Trace("to-core-result") << "core: " << c << std::endl;
    }
  }
  return std::pair<Result, std::vector<Node>>(result, toCore);
}
SolverEngine* TimeoutCoreManager::getSubSolver() { return d_subSolver.get(); }

void TimeoutCoreManager::includeAssertion(size_t index, bool& removedAssertion)
{
  // should have set index which is not already included
  Assert(index < d_ppAsserts.size());
  Assert(d_ainfo.find(index) == d_ainfo.end());
  // initialize the assertion info
  AssertInfo& ainext = d_ainfo[index];
  // we assume it takes the current model
  size_t currModelIndex = d_modelValues.size() - 1;
  d_modelToAssert[currModelIndex] = index;
  ainext.d_coverModels++;
  Trace("smt-to-core") << "Add assertion #" << index << ": "
                       << d_ppAsserts[index] << std::endl;

  // iterate over previous models
  std::unordered_map<size_t, size_t>::iterator itp;
  std::map<size_t, AssertInfo>::iterator ita;
  for (size_t i = 0; i < currModelIndex; i++)
  {
    Assert(d_modelValues[i].size() == d_ppAsserts.size());
    Node vic = d_modelValues[i][index];
    // determine if this assertion should take ownership of the i^th model
    bool coverModel = false;
    if (vic == d_false)
    {
      // we take all models we were false on
      coverModel = true;
    }
    else if (vic.isNull() && d_unkModels.find(i) != d_unkModels.end())
    {
      // we take models we were unknown on that did not have a false assertion
      coverModel = true;
    }
    if (coverModel)
    {
      // decrement the count of the assertion that previously owned it
      itp = d_modelToAssert.find(i);
      Assert(itp != d_modelToAssert.end());
      Assert(itp->second != index);
      ita = d_ainfo.find(itp->second);
      Assert(ita != d_ainfo.end());
      ita->second.d_coverModels--;
      if (ita->second.d_coverModels == 0)
      {
        Trace("smt-to-core")
            << "Remove assertion #" << itp->second << std::endl;
        // a previous assertion no longer is necessary
        d_ainfo.erase(ita);
        removedAssertion = true;
      }
      d_modelToAssert[i] = index;
      ainext.d_coverModels++;
    }
  }
  Trace("smt-to-core") << "...covers " << ainext.d_coverModels << " models"
                       << std::endl;
}

void TimeoutCoreManager::getNextAssertions(
    const std::vector<size_t>& nextInclude, std::vector<Node>& nextAsserts)
{
  if (d_modelValues.empty())
  {
    // empty initially
    return;
  }
  Trace("smt-to-core") << "Get next assertions..." << std::endl;
  bool removedAssertion = false;
  // include each assertion, which may trigger other formulas to be removed
  // from our active set (given by d_ainfo).
  for (size_t i : nextInclude)
  {
    includeAssertion(i, removedAssertion);
  }

  // now have a list of assertions to include
  for (std::pair<const size_t, AssertInfo>& a : d_ainfo)
  {
    Assert(a.first < d_ppAsserts.size());
    Assert(a.second.d_coverModels > 0);
    Node pa = d_ppAsserts[a.first];
    nextAsserts.push_back(pa);
  }
  if (removedAssertion)
  {
    // we have to recompute symbols from scratch
    d_asymbols.clear();
    for (std::pair<const size_t, AssertInfo>& a : d_ainfo)
    {
      std::unordered_set<Node>& syms = d_syms[a.first];
      d_asymbols.insert(syms.begin(), syms.end());
    }
  }
  else
  {
    // otherwise, add to current symbols
    for (size_t i : nextInclude)
    {
      const std::unordered_set<Node>& syms = d_syms[i];
      d_asymbols.insert(syms.begin(), syms.end());
    }
  }

  // include the skolem definitions
  getActiveDefinitions(nextAsserts);

  Trace("smt-to-core")
      << "...finished get next assertions, #current assertions = "
      << d_ainfo.size() << ", #free variables = " << d_asymbols.size()
      << ", #asserts and defs=" << nextAsserts.size() << std::endl;
}

void TimeoutCoreManager::getActiveDefinitions(std::vector<Node>& nextAsserts)
{
  if (!d_skolemToAssert.empty())
  {
    std::map<Node, Node>::const_iterator itk;
    for (const Node& s : d_asymbols)
    {
      itk = d_skolemToAssert.find(s);
      // avoid duplicates, as a skolem definition may have been added as an
      // ordinary assertion
      if (itk != d_skolemToAssert.end()
          && std::find(nextAsserts.begin(), nextAsserts.end(), itk->second)
                 == nextAsserts.end())
      {
        nextAsserts.push_back(itk->second);
      }
    }
  }
  nextAsserts.insert(
      nextAsserts.end(), d_globalInclude.begin(), d_globalInclude.end());
}

Result TimeoutCoreManager::checkSatNext(const std::vector<Node>& nextAssertions,
                                        std::vector<size_t>& nextInclude)
{
  verbose(1) << "TimeoutCoreManager::checkSatNext, #assertions="
             << nextAssertions.size() << ", #models=" << d_modelValues.size()
             << std::endl;
  Trace("smt-to-core") << "--- checkSatNext #models=" << d_modelValues.size()
                       << std::endl;
  Trace("smt-to-core") << "checkSatNext: preprocess" << std::endl;
  d_subSolver.reset(nullptr);
  Result result;
  theory::initializeSubsolver(
      d_subSolver, d_env, true, options().smt.toCoreTimeout);
  d_subSolver->setOption("produce-models", "true");
  Trace("smt-to-core") << "checkSatNext: assert to subsolver" << std::endl;
  for (const Node& a : nextAssertions)
  {
    d_subSolver->assertFormula(a);
  }
  Trace("smt-to-core") << "checkSatNext: check with subsolver" << std::endl;
  result = d_subSolver->checkSat();
  Trace("smt-to-core") << "checkSatNext: ...result is " << result << std::endl;
  if (result.getStatus() == Result::UNKNOWN
      && result.getUnknownExplanation() == UnknownExplanation::TIMEOUT)
  {
    if (isOutputOn(OutputTag::TIMEOUT_CORE_BENCHMARK))
    {
      std::vector<Node> bench(nextAssertions.begin(), nextAssertions.end());
      std::stringstream ss;
      smt::PrintBenchmark pb(Printer::getPrinter(ss));
      pb.printBenchmark(ss, d_env.getLogicInfo().getLogicString(), {}, bench);
      output(OutputTag::TIMEOUT_CORE_BENCHMARK)
          << ";; timeout core" << std::endl;
      output(OutputTag::TIMEOUT_CORE_BENCHMARK) << ss.str();
      output(OutputTag::TIMEOUT_CORE_BENCHMARK)
          << ";; end timeout core" << std::endl;
    }
    // will terminate with unknown (timeout)
    return result;
  }
  // if UNSAT, we are done
  if (result.getStatus() == Result::UNSAT)
  {
    // keep core, which is an unsat core?
    Trace("smt-to-core") << "...return, UNSAT" << std::endl;
    return result;
  }
  Trace("smt-to-core") << "checkSatNext: recordCurrentModel" << std::endl;
  bool allAssertsSat;
  if (recordCurrentModel(allAssertsSat, nextInclude))
  {
    Trace("smt-to-core") << "...return, check again" << std::endl;
    return Result(Result::UNKNOWN, UnknownExplanation::REQUIRES_CHECK_AGAIN);
  }
  else if (allAssertsSat)
  {
    // core is discarded if we terminate with sat
    d_ainfo.clear();
    Trace("smt-to-core") << "...return, SAT" << std::endl;
    // a model happened to satisfy every assertion
    return Result(Result::SAT);
  }
  else
  {
    Trace("smt-to-core") << "...return, (fail) " << result << std::endl;
  }
  // core is discarded if we terminate with sat/unknown
  d_ainfo.clear();
  // Otherwise, we take the current result (likely unknown).
  // If result happens to be sat, then we are in a case where the model doesnt
  // satisfy an assertion that was included, in which case we trust the
  // checkSatInternal result.
  return result;
}

void TimeoutCoreManager::initializeAssertions(
    const std::vector<Node>& ppAsserts,
    const std::map<size_t, Node>& ppSkolemMap,
    const std::vector<Node>& assumptions)
{
  bool hasAssumptions = !assumptions.empty();
  if (TraceIsOn("smt-to-core"))
  {
    Trace("smt-to-core") << "initializeAssertions" << std::endl;
    if (hasAssumptions)
    {
      Trace("smt-to-core") << "#assumptions =" << assumptions << std::endl;
    }
    Trace("smt-to-core") << "#ppAsserts = " << ppAsserts.size() << std::endl;
  }
  std::vector<Node> skDefs;
  const std::vector<Node>& input = hasAssumptions ? assumptions : ppAsserts;
  std::map<size_t, Node>::const_iterator itc;
  theory::TrustSubstitutionMap& tls = d_env.getTopLevelSubstitutions();
  for (size_t i = 0, nasserts = input.size(); i < nasserts; i++)
  {
    Node pa = input[i];
    Node par = rewrite(tls.get().apply(pa));
    if (pa.isConst())
    {
      if (pa.getConst<bool>())
      {
        // ignore true assertions
        continue;
      }
      else
      {
        // false assertion, we are done
        d_ppAsserts.clear();
        d_ppAsserts.push_back(par);
        d_ppAssertsOrig.push_back(pa);
        break;
      }
    }
    if (hasAssumptions)
    {
      d_ppAsserts.push_back(par);
      d_ppAssertsOrig.push_back(pa);
    }
    else
    {
      itc = ppSkolemMap.find(i);
      if (itc == ppSkolemMap.end())
      {
        d_ppAsserts.push_back(par);
        d_ppAssertsOrig.push_back(pa);
      }
      else
      {
        d_skolemToAssert[itc->second] = pa;
        skDefs.push_back(pa);
      }
    }
  }
  if (hasAssumptions)
  {
    d_globalInclude = ppAsserts;
  }
  // remember the size of the prefix of non-skolem definitions
  d_numAssertsNsk = d_ppAsserts.size();
  // now, append the skolem definitions to the end of the assertion list
  d_ppAsserts.insert(d_ppAsserts.end(), skDefs.begin(), skDefs.end());
  d_ppAssertsOrig.insert(d_ppAssertsOrig.end(), skDefs.begin(), skDefs.end());
  Trace("smt-to-core") << "get symbols..." << std::endl;
  for (size_t i = 0, npasserts = d_ppAsserts.size(); i < npasserts; i++)
  {
    expr::getSymbols(d_ppAsserts[i], d_syms[i]);
  }
  Trace("smt-to-core") << "after processing, #asserts = " << d_ppAsserts.size()
                       << ", #skolem-defs = " << d_skolemToAssert.size()
                       << std::endl;
}

bool TimeoutCoreManager::recordCurrentModel(bool& allAssertsSat,
                                            std::vector<size_t>& nextInclude)
{
  nextInclude.clear();
  // allocate the model value vector
  d_modelValues.emplace_back();
  std::vector<Node>& currModel = d_modelValues.back();
  allAssertsSat = true;
  size_t indexScore = 0;
  size_t nasserts = d_ppAsserts.size();
  size_t startIndex =
      nasserts == 0 ? 0 : Random::getRandom().pick(0, nasserts - 1);
  currModel.resize(nasserts);
  bool hadFalseAssert = false;
  for (size_t i = 0; i < nasserts; i++)
  {
    size_t ii = (i + startIndex) % nasserts;
    Node a = d_ppAsserts[ii];
    Node av = d_subSolver->getValue(a);
    Trace("smt-to-core-mv") << "M(" << a << ") = " << av << std::endl;
    av = av.isConst() ? av : Node::null();
    currModel[ii] = av;
    if (av == d_true)
    {
      continue;
    }
    allAssertsSat = false;
    bool isFalse = (av == d_false);
    hadFalseAssert = hadFalseAssert || isFalse;
    // if its already included in our assertions
    if (d_ainfo.find(ii) != d_ainfo.end())
    {
      // we were unable to satisfy this assertion; the result from the last
      // check-sat was likely "unknown", we skip this assertion and look for
      // a different one
      continue;
    }
    // 7 is the max value for indexScore as computed below
    if (indexScore == 7 || (!nextInclude.empty() && i >= d_numAssertsNsk))
    {
      // already max score, or we found a normal assertion
      continue;
    }
    // prefer false over unknown, shared symbols over no shared symbols
    size_t currScore = (isFalse ? 1 : 0) + (hasCurrentSharedSymbol(ii) ? 2 : 0)
                       + (i >= d_numAssertsNsk ? 0 : 4);
    Trace("smt-to-core-debug") << "score " << currScore << std::endl;
    if (!nextInclude.empty() && indexScore >= currScore)
    {
      continue;
    }
    // include this one, remembering if it is false or not
    indexScore = currScore;
    nextInclude.clear();
    nextInclude.push_back(ii);
  }
  Trace("smt-to-core") << "selected new assertion, score=" << indexScore
                       << std::endl;
  // if we did not find a false assertion, remember it
  if (!allAssertsSat && !hadFalseAssert)
  {
    d_unkModels.insert(d_modelValues.size());
  }

  // Note we could consider updating d_asymbols to contain only the symbols
  // in the relevant assertions of the subsolver here as a heuristic.

  // we are successful if we have a new assertion to include
  return !nextInclude.empty();
}

bool TimeoutCoreManager::hasCurrentSharedSymbol(size_t i) const
{
  std::map<size_t, std::unordered_set<Node>>::const_iterator it =
      d_syms.find(i);
  if (it == d_syms.end())
  {
    return false;
  }
  const std::unordered_set<Node>& syms = it->second;
  for (const Node& n : syms)
  {
    if (d_asymbols.find(n) != d_asymbols.end())
    {
      return true;
    }
  }
  return false;
}

}  // namespace smt
}  // namespace cvc5::internal
