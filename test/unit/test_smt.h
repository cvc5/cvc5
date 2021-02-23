/*********************                                                        */
/*! \file test_smt.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common header for unit tests that need an SmtEngine.
 **/

#ifndef CVC4__TEST__UNIT__TEST_SMT_H
#define CVC4__TEST__UNIT__TEST_SMT_H

#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "test.h"

namespace CVC4 {
namespace test {

class TestSmt : public TestInternal
{
 protected:
  void SetUp() override
  {
    d_nodeManager.reset(new NodeManager(nullptr));
    d_scope.reset(new NodeManagerScope(d_nodeManager.get()));
    d_smtEngine.reset(new SmtEngine(d_nodeManager.get()));
    d_smtEngine->finishInit();
  }

  std::unique_ptr<NodeManagerScope> d_scope;
  std::unique_ptr<NodeManager> d_nodeManager;
  std::unique_ptr<SmtEngine> d_smtEngine;
};
}  // namespace test
}  // namespace CVC4
#endif
