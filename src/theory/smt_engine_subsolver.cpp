/*********************                                                        */
/*! \file smt_engine_subsolver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utilities for initializing subsolvers (copies of
 ** SmtEngine) during solving.
 **/

#include "theory/smt_engine_subsolver.h"

#include "api/cvc4cpp.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {

// optimization: try to rewrite to constant
Result quickCheck(Node& query)
{
  query = theory::Rewriter::rewrite(query);
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

void initializeSubsolver(std::unique_ptr<SmtEngine>& smte,
                         bool needsTimeout,
                         unsigned long timeout)
{
  NodeManager* nm = NodeManager::currentNM();
  SmtEngine* smtCurr = smt::currentSmtEngine();
  // must copy the options
  smte.reset(new SmtEngine(nm->toExprManager(), &smtCurr->getOptions()));
  smte->setIsInternalSubsolver();
  smte->setLogic(smtCurr->getLogicInfo());
  if (needsTimeout)
  {
    smte->setTimeLimit(timeout);
  }
  smte->setLogic(smt::currentSmtEngine()->getLogicInfo());
}

Result checkWithSubsolver(std::unique_ptr<SmtEngine>& smte,
                          Node query,
                          bool needsTimeout,
                          unsigned long timeout)
{
  Assert(query.getType().isBoolean());
  Result r = quickCheck(query);
  if (!r.isUnknown())
  {
    return r;
  }
  initializeSubsolver(smte, needsTimeout, timeout);
  smte->assertFormula(query);
  return smte->checkSat();
}

Result checkWithSubsolver(Node query, bool needsTimeout, unsigned long timeout)
{
  std::vector<Node> vars;
  std::vector<Node> modelVals;
  return checkWithSubsolver(query, vars, modelVals, needsTimeout, timeout);
}

Result checkWithSubsolver(Node query,
                          const std::vector<Node>& vars,
                          std::vector<Node>& modelVals,
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
      for (const Node& v : vars)
      {
        modelVals.push_back(v.getType().mkGroundTerm());
      }
    }
    return r;
  }
  std::unique_ptr<SmtEngine> smte;
  initializeSubsolver(smte, needsTimeout, timeout);
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

}  // namespace theory
}  // namespace CVC4
