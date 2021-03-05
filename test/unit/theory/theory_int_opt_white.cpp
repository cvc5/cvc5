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

  OptResult r = d_optslv->checkOpt();

  // We expect max_cost == 99
  ASSERT_EQ(d_optslv->objectiveGetValue(),
                    d_nodeManager->mkConst(Rational("99")));

  std::cout << "Result is :" << r << std::endl;
  std::cout << "Optimized max value is: "
            << d_optslv->objectiveGetValue() << std::endl;
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
  std::cout << "Optimized max value is: "
            << d_optslv->objectiveGetValue() << std::endl;
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
}  // namespace test
}  // namespace CVC4
