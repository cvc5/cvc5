/*********************                                                        */
/*! \file smt_engine_subsolver.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of utilities for initializing subsolvers (copies of
 ** SmtEngine) during solving.
 **/

#include "theory/smt_engine_subsolver.h"

#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace theory {

// optimization: try to rewrite to constant 
Result quickCheck(Expr& query)
{
  query = theory::Rewriter::rewrite(Node::fromExpr(query)).toExpr();
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
  return Result(Result::SAT_UNKNOWN);
}
  
void initializeSubsolverWithExport(std::unique_ptr<SmtEngine>& smte,
                                   ExprManager& em,
                                   ExprManagerMapCollection& varMap,
                                   Expr query,
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
    smte.reset(new SmtEngine(&em));
    smte->setIsInternalSubsolver();
    if (needsTimeout)
    {
      smte->setTimeLimit(timeout, true);
    }
    smte->setLogic(smt::currentSmtEngine()->getLogicInfo());
    Expr equery = query.exportTo(&em, varMap);
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

void initializeSubsolver(std::unique_ptr<SmtEngine>& smte, Expr query)
{
  NodeManager* nm = NodeManager::currentNM();
  smte.reset(new SmtEngine(nm->toExprManager()));
  smte->setIsInternalSubsolver();
  smte->assertFormula(query);
}

Result checkWithSubsolver(std::unique_ptr<SmtEngine>& smte, Expr query)
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

Result checkWithSubsolver(Expr query,
                          bool needsTimeout,
                          unsigned long timeout)
{
  Assert(query.getType().isBoolean());
  Result r = quickCheck(query);
  if (!r.isUnknown())
  {
    return r;
  }
  std::unique_ptr<SmtEngine> smte;
  if (needsTimeout)
  {
    ExprManagerMapCollection varMap;
    NodeManager* nm = NodeManager::currentNM();
    ExprManager em(nm->getOptions());
    initializeSubsolverWithExport(smte,em,varMap,query,needsTimeout,timeout);
  }
  else
  {
    initializeSubsolver(smte,query);
  }
  return smte->checkSat();
}

Result checkWithSubsolver(Expr query,
                          const std::vector<Expr>& vars,
                          std::vector<Expr>& modelVals,
                                   bool needsTimeout,
                                   unsigned long timeout)
{
  Assert(query.getType().isBoolean());
  Result r = quickCheck(query);
  if (!r.isUnknown())
  {
    return r;
  }
  std::unique_ptr<SmtEngine> smte;
  ExprManagerMapCollection varMap;
  NodeManager* nm = NodeManager::currentNM();
  ExprManager em(nm->getOptions());
  bool needsExport = false;
  if (needsTimeout)
  {
    needsExport = true;
    initializeSubsolverWithExport(smte,em,varMap,query,needsTimeout,timeout);
  }
  else
  {
    initializeSubsolver(smte,query);
  }
  r = smte->checkSat();
  modelVals.clear();
  if (r.asSatisfiabilityResult().isSat() == Result::SAT)
  {
    for (const Expr& v : vars)
    {
      Expr val;
      if (needsExport)
      {
        Expr ev = v.exportTo(&em, varMap);
        val = smte->getValue(ev).exportTo(
            nm->toExprManager(), varMap);
      }
      else
      {
        val = smte->getValue(v);
      }
      modelVals.push_back(val);
    }
  }
  return r;
}

} 
}  // namespace CVC4
