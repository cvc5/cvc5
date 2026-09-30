/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Tests for the lifetime and solver isolation of recursive definitions.
 */

#include "smt/env.h"
#include "test_smt.h"
#include "util/result.h"

namespace cvc5::internal::test {

class TestTheoryRecursiveFunctions : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("incremental", "true");
    d_slvEngine->setOption("fmf-fun", "true");
    d_slvEngine->setOption("macros-quant", "true");
    d_slvEngine->finishInit();
    d_x = d_nodeManager->mkBoundVar(d_nodeManager->integerType());
    d_f = NodeManager::mkDummySkolem(
        "f",
        d_nodeManager->mkFunctionType(d_nodeManager->integerType(),
                                      d_nodeManager->booleanType()));
  }
  Node d_x;
  Node d_f;
};

TEST_F(TestTheoryRecursiveFunctions, localDefinition)
{
  Env& env = d_slvEngine->getEnv();
  EXPECT_FALSE(env.isRecursiveFunction(d_f));
  d_slvEngine->push();
  d_slvEngine->defineFunctionRec(d_f, {d_x}, d_nodeManager->mkConst(true));
  EXPECT_TRUE(env.isRecursiveFunction(d_f));
  EXPECT_EQ(d_slvEngine->checkSat().getStatus(), Result::SAT);
  d_slvEngine->pop();
  EXPECT_FALSE(env.isRecursiveFunction(d_f));
  d_slvEngine->defineFunctionRec(d_f, {d_x}, d_nodeManager->mkConst(false));
  EXPECT_TRUE(env.isRecursiveFunction(d_f));
  d_slvEngine->resetAssertions();
  EXPECT_FALSE(env.isRecursiveFunction(d_f));
}

TEST_F(TestTheoryRecursiveFunctions, globalDefinition)
{
  Env& env = d_slvEngine->getEnv();
  d_slvEngine->push();
  d_slvEngine->defineFunctionRec(
      d_f, {d_x}, d_nodeManager->mkConst(true), true);
  EXPECT_EQ(d_slvEngine->checkSat().getStatus(), Result::SAT);
  EXPECT_TRUE(env.isRecursiveFunction(d_f));
  d_slvEngine->pop();
  EXPECT_EQ(d_slvEngine->checkSat().getStatus(), Result::SAT);
  EXPECT_TRUE(env.isRecursiveFunction(d_f));
  d_slvEngine->resetAssertions();
  EXPECT_EQ(d_slvEngine->checkSat().getStatus(), Result::SAT);
  EXPECT_TRUE(env.isRecursiveFunction(d_f));
}

TEST_F(TestTheoryRecursiveFunctions, sharedNodeManager)
{
  d_slvEngine->defineFunctionRec(d_f, {d_x}, d_nodeManager->mkConst(true));
  SolverEngine other(d_nodeManager.get());
  other.setOption("fmf-fun", "true");
  other.setOption("macros-quant", "true");
  other.finishInit();
  EXPECT_TRUE(d_slvEngine->getEnv().isRecursiveFunction(d_f));
  EXPECT_FALSE(other.getEnv().isRecursiveFunction(d_f));
  other.defineFunctionsRec({d_f}, {{d_x}}, {d_nodeManager->mkConst(false)});
  EXPECT_TRUE(other.getEnv().isRecursiveFunction(d_f));
  d_slvEngine->resetAssertions();
  EXPECT_FALSE(d_slvEngine->getEnv().isRecursiveFunction(d_f));
  EXPECT_TRUE(other.getEnv().isRecursiveFunction(d_f));
}

}  // namespace cvc5::internal::test
