/*********************                                                        */
/*! \file test_expr.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common header for Expr unit tests.
 **/

#ifndef CVC4__TEST__UNIT__TEST_EXPR_H
#define CVC4__TEST__UNIT__TEST_EXPR_H

#include "expr/expr_manager.h"
#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "test.h"
#include "test_api.h"

namespace CVC4 {
namespace test {

class TestExprBlack : public TestApi
{
 protected:
  void SetUp() override
  {
    d_exprManager = d_solver.getExprManager();
    d_nodeManager = NodeManager::fromExprManager(d_exprManager);
    d_smtEngine = d_solver.getSmtEngine();
    d_scope.reset(new smt::SmtScope(d_smtEngine));
  }
  std::unique_ptr<smt::SmtScope> d_scope;
  ExprManager* d_exprManager;
  NodeManager* d_nodeManager;
  SmtEngine* d_smtEngine;
};

class TestExprWhite : public TestApi
{
 protected:
  void SetUp() override
  {
    d_nodeManager.reset(new NodeManager(nullptr));
    d_scope.reset(new NodeManagerScope(d_nodeManager.get()));
  }
  std::unique_ptr<NodeManager> d_nodeManager;
  std::unique_ptr<NodeManagerScope> d_scope;
};

}  // namespace test
}  // namespace CVC4
#endif
