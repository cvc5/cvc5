/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of utilities for initializing subsolvers (copies of
 * SolverEngine) during solving.
 */

#include "theory/smt_engine_subsolver.h"

#include "proof/unsat_core.h"
#include "smt/env.h"
#include "smt/solver_engine.h"
#include "smt/solver_engine_scope.h"

namespace cvc5 {
namespace theory {

// optimization: try to rewrite to constant
Result quickCheck(Node& query)
{
  if (query.isConst())
  {
    if (!query.getConst<bool>())
    {
      return Result(Result::UNSAT);
    }
    else
    {
      return Result(Result::SAT);
    }
  }
  return Result(Result::SAT_UNKNOWN, Result::REQUIRES_FULL_CHECK);
}

void initializeSubsolver(std::unique_ptr<SolverEngine>& smte,
                         const Options& opts,
                         const LogicInfo& logicInfo,
                         bool needsTimeout,
                         unsigned long timeout)
{
  NodeManager* nm = NodeManager::currentNM();
  smte.reset(new SolverEngine(nm, &opts));
  smte->setIsInternalSubsolver();
  smte->setLogic(logicInfo);
  // set the options
  if (needsTimeout)
  {
    smte->setTimeLimit(timeout);
  }
}
void initializeSubsolver(std::unique_ptr<SolverEngine>& smte,
                         const Env& env,
                         bool needsTimeout,
                         unsigned long timeout)
{
  initializeSubsolver(
      smte, env.getOptions(), env.getLogicInfo(), needsTimeout, timeout);
}

Result checkWithSubsolver(std::unique_ptr<SolverEngine>& smte,
                          Node query,
                          const Options& opts,
                          const LogicInfo& logicInfo,
                          bool needsTimeout,
                          unsigned long timeout)
{
  Assert(query.getType().isBoolean());
  Result r = quickCheck(query);
  if (!r.isUnknown())
  {
    return r;
  }
  initializeSubsolver(smte, opts, logicInfo, needsTimeout, timeout);
  smte->assertFormula(query);
  return smte->checkSat();
}

Result checkWithSubsolver(Node query,
                          const Options& opts,
                          const LogicInfo& logicInfo,
                          bool needsTimeout,
                          unsigned long timeout)
{
  std::vector<Node> vars;
  std::vector<Node> modelVals;
  return checkWithSubsolver(
      query, vars, modelVals, opts, logicInfo, needsTimeout, timeout);
}

Result checkWithSubsolver(Node query,
                          const std::vector<Node>& vars,
                          std::vector<Node>& modelVals,
                          const Options& opts,
                          const LogicInfo& logicInfo,
                          bool needsTimeout,
                          unsigned long timeout)
{
  Assert(query.getType().isBoolean());
  Assert(modelVals.empty());
  // ensure clear
  modelVals.clear();
  Result r = quickCheck(query);
  if (!r.isUnknown())
  {
    if (r.asSatisfiabilityResult().isSat() == Result::SAT)
    {
      // default model
      NodeManager* nm = NodeManager::currentNM();
      for (const Node& v : vars)
      {
        modelVals.push_back(nm->mkGroundTerm(v.getType()));
      }
    }
    return r;
  }
  std::unique_ptr<SolverEngine> smte;
  initializeSubsolver(smte, opts, logicInfo, needsTimeout, timeout);
  smte->assertFormula(query);
  r = smte->checkSat();
  if (r.asSatisfiabilityResult().isSat() == Result::SAT)
  {
    for (const Node& v : vars)
    {
      Node val = smte->getValue(v);
      modelVals.push_back(val);
    }
  }
  return r;
}

void getModelFromSubsolver(SolverEngine& smt,
                           const std::vector<Node>& vars,
                           std::vector<Node>& vals)
{
  for (const Node& v : vars)
  {
    Node mv = smt.getValue(v);
    vals.push_back(mv);
  }
}

bool getUnsatCoreFromSubsolver(SolverEngine& smt,
                               const std::unordered_set<Node>& queryAsserts,
                               std::vector<Node>& uasserts)
{
  UnsatCore uc = smt.getUnsatCore();
  bool hasQuery = false;
  for (UnsatCore::const_iterator i = uc.begin(); i != uc.end(); ++i)
  {
    Node uassert = *i;
    if (queryAsserts.find(uassert) != queryAsserts.end())
    {
      hasQuery = true;
      continue;
    }
    uasserts.push_back(uassert);
  }
  return hasQuery;
}

void getUnsatCoreFromSubsolver(SolverEngine& smt, std::vector<Node>& uasserts)
{
  std::unordered_set<Node> queryAsserts;
  getUnsatCoreFromSubsolver(smt, queryAsserts, uasserts);
}

}  // namespace theory
}  // namespace cvc5
