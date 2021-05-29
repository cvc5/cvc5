/******************************************************************************
 * Top contributors (to current version):
 *   Michael Chang, Yancheng Ou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White-box testing for optimization module for Integers.
 */
#include <iostream>

#include "smt/optimization_solver.h"
#include "test_smt.h"
#include "util/rational.h"

namespace cvc5 {

using namespace theory;
using namespace smt;

namespace test {

class TestTheoryWhiteIntOpt : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_smtEngine->setOption("produce-assertions", "true");
    d_smtEngine->finishInit();

    d_optslv.reset(new OptimizationSolver(d_smtEngine.get()));
    d_intType.reset(new TypeNode(d_nodeManager->integerType()));
  }

  std::unique_ptr<OptimizationSolver> d_optslv;
  std::unique_ptr<TypeNode> d_intType;
};

TEST_F(TestTheoryWhiteIntOpt, max)
{
  Node ub = d_nodeManager->mkConst(Rational("100"));
  Node lb = d_nodeManager->mkConst(Rational("0"));

  // Objectives to be optimized max_cost is max objective
  Node max_cost = d_nodeManager->mkVar(*d_intType);

  Node upb = d_nodeManager->mkNode(kind::GT, ub, max_cost);
  Node lowb = d_nodeManager->mkNode(kind::GT, max_cost, lb);

  /* Result of asserts is:
      0 < max_cost < 100
  */
  d_smtEngine->assertFormula(upb);
  d_smtEngine->assertFormula(lowb);

  // We activate our objective so the subsolver knows to optimize it
  d_optslv->addObjective(max_cost, OptimizationObjective::MAXIMIZE);

  OptimizationResult::ResultType r = d_optslv->checkOpt();

  ASSERT_EQ(r, OptimizationResult::OPTIMAL);

  // We expect max_cost == 99
  ASSERT_EQ(d_optslv->getValues()[0].getValue().getConst<Rational>(),
            Rational("99"));

  d_optslv->resetObjectives();
}

TEST_F(TestTheoryWhiteIntOpt, min)
{
  Node ub = d_nodeManager->mkConst(Rational("100"));
  Node lb = d_nodeManager->mkConst(Rational("0"));

  // Objectives to be optimized max_cost is max objective
  Node max_cost = d_nodeManager->mkVar(*d_intType);

  Node upb = d_nodeManager->mkNode(kind::GT, ub, max_cost);
  Node lowb = d_nodeManager->mkNode(kind::GT, max_cost, lb);

  /* Result of asserts is:
      0 < max_cost < 100
  */
  d_smtEngine->assertFormula(upb);
  d_smtEngine->assertFormula(lowb);

  // We activate our objective so the subsolver knows to optimize it
  d_optslv->addObjective(max_cost, OptimizationObjective::MINIMIZE);

  OptimizationResult::ResultType r = d_optslv->checkOpt();

  ASSERT_EQ(r, OptimizationResult::OPTIMAL);

  // We expect max_cost == 99
  ASSERT_EQ(d_optslv->getValues()[0].getValue().getConst<Rational>(),
            Rational("1"));

  d_optslv->resetObjectives();
}

TEST_F(TestTheoryWhiteIntOpt, result)
{
  Node ub = d_nodeManager->mkConst(Rational("100"));
  Node lb = d_nodeManager->mkConst(Rational("0"));

  // Objectives to be optimized max_cost is max objective
  Node max_cost = d_nodeManager->mkVar(*d_intType);

  Node upb = d_nodeManager->mkNode(kind::GT, lb, max_cost);
  Node lowb = d_nodeManager->mkNode(kind::GT, max_cost, ub);

  /* Result of asserts is:
      0 > max_cost > 100
  */
  d_smtEngine->assertFormula(upb);
  d_smtEngine->assertFormula(lowb);

  // We activate our objective so the subsolver knows to optimize it
  d_optslv->addObjective(max_cost, OptimizationObjective::MAXIMIZE);

  // This should return OPT_UNSAT since 0 > x > 100 is impossible.
  OptimizationResult::ResultType r = d_optslv->checkOpt();

  // We expect our check to have returned UNSAT
  ASSERT_EQ(r, OptimizationResult::UNSAT);
  d_optslv->resetObjectives();
}

TEST_F(TestTheoryWhiteIntOpt, open_interval)
{
  Node ub1 = d_nodeManager->mkConst(Rational("100"));
  Node lb1 = d_nodeManager->mkConst(Rational("0"));
  Node lb2 = d_nodeManager->mkConst(Rational("110"));

  Node cost1 = d_nodeManager->mkVar(*d_intType);
  Node cost2 = d_nodeManager->mkVar(*d_intType);

  /* Result of assertion is:
      0 < cost1 < 100
      110 < cost2
  */
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::LT, lb1, cost1));
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::LT, cost1, ub1));

  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::LT, lb2, cost2));

  /* Optimization objective:
      cost1 + cost2
  */
  Node cost3 = d_nodeManager->mkNode(kind::PLUS, cost1, cost2);

  d_optslv->addObjective(cost3, OptimizationObjective::MINIMIZE);

  OptimizationResult::ResultType r = d_optslv->checkOpt();

  ASSERT_EQ(r, OptimizationResult::OPTIMAL);

  // expect the minimum result of cost3 = cost1 + cost2 to be 1 + 111 = 112
  ASSERT_EQ(d_optslv->getValues()[0].getValue().getConst<Rational>(),
            Rational("112"));
  d_optslv->resetObjectives();
}

}  // namespace test
}  // namespace cvc5
