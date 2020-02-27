/*********************                                                        */
/*! \file expr_miner.cpp
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

#include "smt_util/smt_engine_subsolver.h"

#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

namespace CVC4 {

void initializeSubsolverWithExport(std::unique_ptr<SmtEngine>& smte,
                                   ExprManager& em,
                                   ExprManagerMapCollection& varMap,
                                   Expr query,
                                   bool needsTimeout,
                                   unsigned long timeout)
{
  // To support a separate timeout for the subsolver, we need to create
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

}  // namespace CVC4
