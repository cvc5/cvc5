/*********************                                                        */
/*! \file smt_engine_subsolver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

void initializeSubsolver(SmtEngine* smte)
{
  smte->setIsInternalSubsolver();
  smte->setLogic(smt::currentSmtEngine()->getLogicInfo());
}

void initializeSubsolverWithExport(SmtEngine* smte,
                                   ExprManager* em,
                                   ExprManagerMapCollection& varMap,
                                   Node query,
                                   bool needsTimeout,
                                   unsigned long timeout)
{
  // To support a separate timeout for the subsolver, we need to use
  // a separate ExprManager with its own options. This requires that
  // the expressions sent to the subsolver can be exported from on
  // ExprManager to another. If the export fails, we throw an
  // OptionException.
  try
  {
    smte->setIsInternalSubsolver();
    if (needsTimeout)
    {
      smte->setTimeLimit(timeout, true);
    }
    smte->setLogic(smt::currentSmtEngine()->getLogicInfo());
    Expr equery = query.toExpr().exportTo(em, varMap);
    smte->assertFormula(equery);
  }
  catch (const CVC4::ExportUnsupportedException& e)
  {
    std::stringstream msg;
    msg << "Unable to export " << query
        << " but exporting expressions is "
           "required for a subsolver.";
    throw OptionException(msg.str());
  }
}

void initializeSubsolver(SmtEngine* smte, Node query)
{
  initializeSubsolver(smte);
  smte->assertFormula(query.toExpr());
}

Result checkWithSubsolver(SmtEngine* smte, Node query)
{
  Assert(query.getType().isBoolean());
  Result r = quickCheck(query);
  if (!r.isUnknown())
  {
    return r;
  }
  initializeSubsolver(smte, query);
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

  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  // This is only temporarily until we have separate options for each
  // SmtEngine instance. We should reuse the same ExprManager with
  // a different SmtEngine (and different options) here, eventually.
  // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
  std::unique_ptr<SmtEngine> simpleSmte;
  std::unique_ptr<api::Solver> slv;
  ExprManager* em = nullptr;
  SmtEngine* smte = nullptr;
  ExprManagerMapCollection varMap;
  NodeManager* nm = NodeManager::currentNM();
  bool needsExport = false;
  if (needsTimeout)
  {
    slv.reset(new api::Solver(&nm->getOptions()));
    em = slv->getExprManager();
    smte = slv->getSmtEngine();
    needsExport = true;
    initializeSubsolverWithExport(
        smte, em, varMap, query, needsTimeout, timeout);
  }
  else
  {
    em = nm->toExprManager();
    simpleSmte.reset(new SmtEngine(em));
    smte = simpleSmte.get();
    initializeSubsolver(smte, query);
  }
  r = smte->checkSat();
  if (r.asSatisfiabilityResult().isSat() == Result::SAT)
  {
    for (const Node& v : vars)
    {
      Expr val;
      if (needsExport)
      {
        Expr ev = v.toExpr().exportTo(em, varMap);
        val = smte->getValue(ev).exportTo(nm->toExprManager(), varMap);
      }
      else
      {
        val = smte->getValue(v.toExpr());
      }
      modelVals.push_back(Node::fromExpr(val));
    }
  }
  return r;
}

}  // namespace theory
}  // namespace CVC4
