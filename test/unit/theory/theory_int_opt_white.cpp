/*********************                                                        */
/*! \file theory_int_opt_white.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Michael Chang
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White-box testing for optimization module.
 **/
#include <iostream>

#include "smt/optimization_solver.h"
#include "test_smt.h"

namespace CVC4 {

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

  const ObjectiveType max_type = OBJECTIVE_MAXIMIZE;

  // We activate our objective so the subsolver knows to optimize it
  d_optslv->activateObj(max_cost, max_type);

  std::cerr << "a" << std::endl;

  OptResult r = d_optslv->checkOpt();

  // We expect max_cost == 99
  ASSERT_EQ(d_optslv->objectiveGetValue(),
            d_nodeManager->mkConst(Rational("99")));

  std::cout << "Result is :" << r << std::endl;
  std::cout << "Optimized max value is: " << d_optslv->objectiveGetValue()
            << std::endl;
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

  const ObjectiveType min_type = OBJECTIVE_MINIMIZE;

  // We activate our objective so the subsolver knows to optimize it
  d_optslv->activateObj(max_cost, min_type);

  OptResult r = d_optslv->checkOpt();

  // We expect max_cost == 99
  ASSERT_EQ(d_optslv->objectiveGetValue(),
            d_nodeManager->mkConst(Rational("1")));

  std::cout << "Result is :" << r << std::endl;
  std::cout << "Optimized max value is: " << d_optslv->objectiveGetValue()
            << std::endl;
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

  const ObjectiveType max_type = OBJECTIVE_MAXIMIZE;

  // We activate our objective so the subsolver knows to optimize it
  d_optslv->activateObj(max_cost, max_type);

  // This should return OPT_UNSAT since 0 > x > 100 is impossible.
  OptResult r = d_optslv->checkOpt();

  // We expect our check to have returned UNSAT
  ASSERT_EQ(r, OPT_UNSAT);

  std::cout << "Result is :" << r << std::endl;
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

  const ObjectiveType min_type = OBJECTIVE_MINIMIZE;
  d_optslv->activateObj(cost3, min_type);

  OptResult r = d_optslv->checkOpt();

  // expect the minimum result of cost3 = cost1 + cost2 to be 1 + 111 = 112
  ASSERT_EQ(d_optslv->objectiveGetValue(),
            d_nodeManager->mkConst(Rational("112")));
  std::cout << "Result is :" << r << std::endl;
  std::cout << "Optimized min value is: " << d_optslv->objectiveGetValue()
            << std::endl;
}

// Below is a test case for real, but it's not guaranteed to run into completion
// because CVC4 might keep finding "bad" values for real numbers
// especially real has infinite domain!
// TEST_F(TestTheoryWhiteIntOpt, open_interval_real)
// {
//   // WARNING:
//   //   domain is infinite,
//   //   though it's bounded,
//   //   it's still possible not run to completion!
//   Term ub1 = d_slv->mkReal(100);
//   Term lb1 = d_slv->mkReal(0);
//   Term lb2 = d_slv->mkReal(110);
//   Term ub2 = d_slv->mkReal(120);
//
//   Term cost1 = d_slv->mkConst(d_slv->getRealSort(), "cost3");
//   Term cost2 = d_slv->mkConst(d_slv->getRealSort(), "cost4");
//   // 0 <= cost1 <= 100
//   d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LEQ, lb1, cost1));
//   d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LEQ, cost1, ub1));
//   // 110 <= cost2 <= 120
//   d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LEQ, lb2, cost2));
//   d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LEQ, cost2, ub2));
//
//   Term cost3 = d_slv->mkTerm(CVC4::api::PLUS, cost1, cost2);
//
//   const ObjectiveType obj_type = OBJECTIVE_MINIMIZE;
//   d_optslv->activateObj(*cost3.d_node, obj_type);
//
//   OptResult r = d_optslv->checkOpt();
//
//   // TS_ASSERT_EQUALS(ub1, ub2);
//
//   TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(),
//   d_nm->mkConst(Rational(110))); std::cout << "Result is :" << r <<
//   std::endl; std::cout << "Optimized value is: " <<
//   d_optslv->objectiveGetValue()
//             << std::endl;
// }

}  // namespace test
}  // namespace CVC4
