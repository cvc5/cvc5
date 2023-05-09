/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {
namespace theory {

SubsolverSetupInfo::SubsolverSetupInfo(const Options& opts,
                                       const LogicInfo& logicInfo,
                                       TypeNode sepLocType,
                                       TypeNode sepDataType)
    : d_opts(opts),
      d_logicInfo(logicInfo),
      d_sepLocType(sepLocType),
      d_sepDataType(sepDataType)
{
}

SubsolverSetupInfo::SubsolverSetupInfo(const Env& env)
    : d_opts(env.getOptions()),
      d_logicInfo(env.getLogicInfo()),
      d_sepLocType(env.getSepLocType()),
      d_sepDataType(env.getSepDataType())
{
}

SubsolverSetupInfo::SubsolverSetupInfo(const Env& env, const Options& opts)
    : d_opts(opts),
      d_logicInfo(env.getLogicInfo()),
      d_sepLocType(env.getSepLocType()),
      d_sepDataType(env.getSepDataType())
{
}

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
  return Result(Result::UNKNOWN, UnknownExplanation::REQUIRES_FULL_CHECK);
}

void initializeSubsolver(std::unique_ptr<SolverEngine>& smte,
                         const SubsolverSetupInfo& info,
                         bool needsTimeout,
                         unsigned long timeout)
{
  smte.reset(new SolverEngine(&info.d_opts));
  smte->setIsInternalSubsolver();
  smte->setLogic(info.d_logicInfo);
  // set the options
  if (needsTimeout)
  {
    smte->setTimeLimit(timeout);
  }
  // set up separation logic heap if necessary
  if (!info.d_sepLocType.isNull() && !info.d_sepDataType.isNull())
  {
    smte->declareSepHeap(info.d_sepLocType, info.d_sepDataType);
  }
}
void initializeSubsolver(std::unique_ptr<SolverEngine>& smte,
                         const Env& env,
                         bool needsTimeout,
                         unsigned long timeout)
{
  SubsolverSetupInfo ssi(env);
  initializeSubsolver(smte, ssi, needsTimeout, timeout);
}

Result checkWithSubsolver(std::unique_ptr<SolverEngine>& smte,
                          Node query,
                          const SubsolverSetupInfo& info,
                          bool needsTimeout,
                          unsigned long timeout)
{
  Assert(query.getType().isBoolean());
  Result r = quickCheck(query);
  if (!r.isUnknown())
  {
    return r;
  }
  initializeSubsolver(smte, info, needsTimeout, timeout);
  smte->assertFormula(query);
  return smte->checkSat();
}

Result checkWithSubsolver(Node query,
                          const SubsolverSetupInfo& info,
                          bool needsTimeout,
                          unsigned long timeout)
{
  std::vector<Node> vars;
  std::vector<Node> modelVals;
  return checkWithSubsolver(
      query, vars, modelVals, info, needsTimeout, timeout);
}

Result checkWithSubsolver(Node query,
                          const std::vector<Node>& vars,
                          std::vector<Node>& modelVals,
                          const SubsolverSetupInfo& info,
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
    if (r.getStatus() == Result::SAT)
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
  initializeSubsolver(smte, info, needsTimeout, timeout);
  smte->assertFormula(query);
  r = smte->checkSat();
  if (r.getStatus() == Result::SAT || r.getStatus() == Result::UNKNOWN)
  {
    for (const Node& v : vars)
    {
      Node val = smte->getValue(v);
      modelVals.push_back(val);
    }
  }
  return r;
}

void assertToSubsolver(SolverEngine& subsolver,
                       const std::vector<Node>& core,
                       const std::unordered_set<Node>& defs,
                       const std::unordered_set<Node>& removed)
{
  for (const Node& f : core)
  {
    // check if it is excluded
    if (removed.find(f) != removed.end())
    {
      continue;
    }
    // check if it is an ordinary function definition
    if (defs.find(f) != defs.end())
    {
      if (f.getKind() == kind::EQUAL && f[0].isVar())
      {
        subsolver.defineFunction(f[0], f[1]);
        continue;
      }
    }
    subsolver.assertFormula(f);
  }
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
}  // namespace cvc5::internal
