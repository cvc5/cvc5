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
 * The solver for SMT queries in an SolverEngine.
 */

#include "smt/smt_driver_to_core.h"

#include <fstream>

#include "api/cpp/cvc5_types.h"
#include "options/base_options.h"
#include "prop/prop_engine.h"
#include "options/smt_options.h"
#include "smt/env.h"
#include "smt/smt_solver.h"
#include "smt/solver_engine.h"
#include "theory/smt_engine_subsolver.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"
#include "smt/print_benchmark.h"
#include "printer/printer.h"
#include "util/random.h"
#include "expr/node_algorithm.h"
#include "theory/substitutions.h"

namespace cvc5::internal {
namespace smt {

SmtDriverToCore::SmtDriverToCore(Env& env,
                                       SmtSolver& smt,
                                       ContextManager* ctx)
    : SmtDriver(env, smt, ctx),
      d_initialized(false),
      d_nextIndexToInclude(0),
      d_queryCount(0)
{
  d_true = NodeManager::currentNM()->mkConst(true);
  d_false = NodeManager::currentNM()->mkConst(false);
}


void SmtDriverToCore::getNextAssertions(preprocessing::AssertionPipeline& ap)
{
  if (!d_initialized)
  {
    Trace("smt-min-assert") << "Initialize assertions..." << std::endl;
    // provide all assertions initially
    Assertions& as = d_smt.getAssertions();
    const context::CDList<Node>& al = as.getAssertionList();
    for (const Node& a : al)
    {
      ap.push_back(a, true);
    }
    return;
  }
  Trace("smt-min-assert") << "Get next assertions..." << std::endl;
  // should have set d_nextIndexToInclude which is not already included
  Assert(d_nextIndexToInclude < d_ppAsserts.size());
  Assert(d_ainfo.find(d_nextIndexToInclude) == d_ainfo.end());
  // initialize the assertion info
  AssertInfo& ainext = d_ainfo[d_nextIndexToInclude];
  Assert(!d_modelValues.empty());
  // we assume it takes the current model
  size_t currModelIndex = d_modelValues.size() - 1;
  d_modelToAssert[currModelIndex] = d_nextIndexToInclude;
  ainext.d_coverModels++;
  Trace("smt-min-assert") << "Add assertion #" << d_nextIndexToInclude << ": "
                          << d_ppAsserts[d_nextIndexToInclude] << std::endl;

  // iterate over previous models
  std::unordered_map<size_t, size_t>::iterator itp;
  std::map<size_t, AssertInfo>::iterator ita;
  bool recomputeSymbols = false;
  for (size_t i = 0; i < currModelIndex; i++)
  {
    Assert(d_modelValues[i].size() == d_ppAsserts.size());
    Node vic = d_modelValues[i][d_nextIndexToInclude];
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
      // decrement the count of the assertion
      itp = d_modelToAssert.find(i);
      Assert(itp != d_modelToAssert.end());
      Assert(itp->second != d_nextIndexToInclude);
      ita = d_ainfo.find(itp->second);
      Assert(ita != d_ainfo.end());
      ita->second.d_coverModels--;
      if (ita->second.d_coverModels == 0)
      {
        Trace("smt-min-assert")
            << "Remove assertion #" << itp->second << std::endl;
        // a previous assertion no longer is necessary
        d_ainfo.erase(ita);
        recomputeSymbols = true;
      }
      d_modelToAssert[i] = d_nextIndexToInclude;
      ainext.d_coverModels++;
    }
  }
  Trace("smt-min-assert") << "...covers " << ainext.d_coverModels << " models"
                          << std::endl;

  // now have a list of assertions to include
  if (recomputeSymbols)
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
    std::unordered_set<Node>& syms = d_syms[d_nextIndexToInclude];
    d_asymbols.insert(syms.begin(), syms.end());
  }
    
  Trace("smt-min-assert")
      << "...finished get next assertions, #current assertions = "
      << d_ainfo.size() << ", #free variables = " << d_asymbols.size() << std::endl;
}

Result SmtDriverToCore::checkSatNext(preprocessing::AssertionPipeline& ap)
{
  Assert (d_initialized);
  Trace("smt-min-assert") << "--- checkSatNext #models=" << d_modelValues.size()
                          << std::endl;
  Trace("smt-min-assert") << "checkSatNext: preprocess" << std::endl;
  std::unique_ptr<SolverEngine> subSolver;
  Result result;
  theory::initializeSubsolver(subSolver, d_env, options().smt.smtMinAssertTimeoutWasSetByUser, options().smt.smtMinAssertTimeout);
  subSolver->setOption("smt-min-assert", "false");
  subSolver->setOption("produce-models", "true");
  Trace("smt-min-assert") << "checkSatNext: assert to subsolver" << std::endl;
  for (const Node& a : ap)
  {
    subSolver->assertFormula(a);
  }
  Trace("smt-min-assert") << "checkSatNext: check with subsolver" << std::endl;
  result = subSolver->checkSat();
  Trace("smt-min-assert")
      << "checkSatNext: ...result is " << result << std::endl;
  if (options().smt.dumpSmtMinAssert && result.getStatus() == Result::UNKNOWN)
  {
    Trace("smt-min-assert")
      << "checkSatNext: dump benchmark " << d_queryCount << std::endl;
    std::vector<Node> bench(ap.begin(), ap.end());
    // Print the query to to queryN.smt2
    std::stringstream fname;
    fname << "query" << d_queryCount << ".smt2";
    std::ofstream fs(fname.str(), std::ofstream::out);
    smt::PrintBenchmark pb(Printer::getPrinter(fs));
    pb.printBenchmark(fs, d_env.getLogicInfo().getLogicString(), {}, bench);
    fs.close();
    d_queryCount++;
  }
  // if UNSAT, we are done
  if (result.getStatus() == Result::UNSAT)
  {
    Trace("smt-min-assert") << "...return, UNSAT" << std::endl;
    return result;
  }
  Trace("smt-min-assert") << "checkSatNext: recordCurrentModel" << std::endl;
  bool allAssertsSat;
  if (recordCurrentModel(allAssertsSat, subSolver.get()))
  {
    Trace("smt-min-assert") << "...return, check again" << std::endl;
    return Result(Result::UNKNOWN, UnknownExplanation::REQUIRES_CHECK_AGAIN);
  }
  else if (allAssertsSat)
  {
    Trace("smt-min-assert") << "...return, SAT" << std::endl;
    // a model happened to satisfy every assertion
    return Result(Result::SAT);
  }
  else
  {
    Trace("smt-min-assert") << "...return, (fail) " << result << std::endl;
  }
  // Otherwise, we take the current result (likely unknown).
  // If result happens to be SAT, then we are in a case where the model doesnt
  // satisfy an assertion that was included, in which case we trust the
  // checkSatInternal result.
  return result;
}

void SmtDriverToCore::initializePreprocessedAssertions(const std::vector<Node>& ppAsserts)
{
  d_ppAsserts.clear();

  Trace("smt-min-assert") << "initializePreprocessedAssertions" << std::endl;
  Trace("smt-min-assert") << "# asserts = " << ppAsserts.size() << std::endl;
  theory::SubstitutionMap& sm = d_env.getTopLevelSubstitutions().get();
  for (const Node& pa : ppAsserts)
  {
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
        d_ppAsserts.push_back(pa);
        return;
      }
    }
    // remember the unpreprocessed version
    d_asserts.push_back(pa);
    // apply top-level substitutions
    Node pas = sm.apply(pa);
    if (pas!=pa)
    {
      d_ppAsserts.push_back(rewrite(pas));
    }
    else
    {
      d_ppAsserts.push_back(pa);
    }
  }
  Trace("smt-min-assert") << "get symbols..." << std::endl;
  for (size_t i=0, npasserts = d_ppAsserts.size(); i<npasserts; i++)
  {
    expr::getSymbols(d_ppAsserts[i], d_syms[i]);
  }
}

bool SmtDriverToCore::recordCurrentModel(bool& allAssertsSat,
                                            SolverEngine* subSolver)
{
  // get the model reference
  theory::TheoryModel* m = nullptr;
  if (subSolver == nullptr)
  {
    TheoryEngine* te = d_smt.getTheoryEngine();
    Assert(te != nullptr);
    m = te->getBuiltModel();
  }
  // allocate the model value vector
  d_modelValues.emplace_back();
  std::vector<Node>& currModel = d_modelValues.back();
  d_nextIndexToInclude = 0;
  allAssertsSat = true;
  bool indexSet = false;
  size_t indexScore = 0;
  size_t nasserts = d_ppAsserts.size();
  Assert(nasserts > 0);
  size_t startIndex = Random::getRandom().pick(0, nasserts - 1);
  currModel.resize(nasserts);
  bool hadFalseAssert = false;
  for (size_t i = 0; i < nasserts; i++)
  {
    size_t ii = (i + startIndex) % nasserts;
    Node a = d_ppAsserts[ii];
    Node av;
    // if no subsolver, get from the model of the SMT solver
    if (subSolver == nullptr)
    {
      av = m->getValue(a);
    }
    else
    {
      av = subSolver->getValue(a);
    }
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
    if (indexScore==3)
    {
      // already max score
      continue;
    }
    // prefer false over unknown, shared symbols over no shared symbols
    size_t currScore = (isFalse ? 1 : 0) + (hasCurrentSharedSymbol(ii) ? 2 : 0);
    Trace("smt-min-assert") << "score " << currScore << std::endl;
    if (indexSet && indexScore>=currScore)
    {
      continue;
    }
    // include this one, remembering if it is false or not
    indexScore = currScore;
    d_nextIndexToInclude = ii;
    indexSet = true;
  }
  Trace("smt-min-assert") << "selected new assertion, score=" << indexScore << std::endl;
  // if we did not find a false assertion, remember it
  if (!allAssertsSat && !hadFalseAssert)
  {
    d_unkModels.insert(d_modelValues.size());
  }
  
/*
  if (subSolver != nullptr)
  {
    bool success;
    std::unordered_set<TNode> rasserts =
        subSolver->getRelevantAssertions(success);
    d_asymbols.clear();
    std::unordered_set<TNode> visited;
    for (TNode a : rasserts)
    {
      expr::getSymbols(a, d_asymbols, visited);
    }
  }
*/
  
  // we are successful if we have a new assertion to include
  return indexSet;
}

bool SmtDriverToCore::hasCurrentSharedSymbol(size_t i) const
{
  std::map<size_t, std::unordered_set<Node>>::const_iterator it = d_syms.find(i);
  if (it==d_syms.end())
  {
    return false;
  }
  const std::unordered_set<Node>& syms = it->second;
  for (const Node& n : syms)
  {
    if (d_asymbols.find(n)!=d_asymbols.end())
    {
      return true;
    }
  }
  return false;
}

}  // namespace smt
}  // namespace cvc5::internal
