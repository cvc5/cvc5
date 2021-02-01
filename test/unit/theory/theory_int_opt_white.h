#include <iostream>
#include <cxxtest/TestSuite.h>
#include "api/cvc4cpp.h"
#include "smt/optimization_solver.h"
#include "expr/expr_manager.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/node_value.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

using namespace CVC4;
using namespace smt;
using namespace api;

class omt : public CxxTest::TestSuite {
  NodeManager *d_nm;
  SmtEngine *d_smt;
  SmtScope *d_scope;
  api::Solver* d_slv;
  OptimizationSolver* d_optslv;
 public:
  void setUp() override
  {
    d_slv = new api::Solver();
    d_smt = d_slv->getSmtEngine();
    d_nm = NodeManager::currentNM();
    d_scope = new SmtScope(d_smt);
    d_optslv = new OptimizationSolver(d_smt);

    Options opts;
    d_slv->setOption("produce-assertions", "true");
    d_slv->setOption("incremental", "true");
  }
  void tearDown() override
  {
    delete d_optslv;
    delete d_scope;
    delete d_slv;
  }
  void testOmt()
  {
    Term ub = d_slv->mkReal(100);
    Term lb = d_slv->mkReal(0);

    // Objectives to be optimized max_cost is max objective min_cost is min
    // objective
    Term max_cost = d_slv->mkConst(d_slv->getIntegerSort(), "cost");
    Term min_cost = d_slv->mkConst(d_slv->getIntegerSort(), "cost2");

    Term upb = d_slv->mkTerm(CVC4::api::Kind::GT, ub, max_cost);
    Term lowb = d_slv->mkTerm(CVC4::api::Kind::GT, max_cost, lb);
    Term upb2 = d_slv->mkTerm(CVC4::api::Kind::GT, ub, min_cost);
    Term lowb2 = d_slv->mkTerm(CVC4::api::Kind::GT, min_cost, lb);

    /* Result of asserts is:
       0 < max_cost < 100
       0 < min_cost < 100
    */
    d_slv->assertFormula(upb);
    d_slv->assertFormula(lowb);
    d_slv->assertFormula(upb2);
    d_slv->assertFormula(lowb2);

    // max_type is 1, signifies max_objective
    const int max_type = 1;
    // min_type is 0, signifies min_objective
    const int min_type = 0;

    // reults will hold the result of the first sat call the subsolver makes
    const int result1 = 0;
    const int result2 = 0;

    // We activate both of our objective so the subsolver knows to optimize them
    d_optslv->activateObj(*max_cost.d_node, max_type, result1);
    d_optslv->activateObj(*min_cost.d_node, min_type, result2);

    CVC4::Result r;
    d_optslv->checkOpt(r);

    // We expect max_cost == 99 and min_cost == 1
    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(*max_cost.d_node),
                     d_nm->mkConst(Rational(99)));
    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(*min_cost.d_node),
                     d_nm->mkConst(Rational(1)));

    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized max value is: "
              << d_optslv->objectiveGetValue(*max_cost.d_node) << std::endl;
    std::cout << "Optimized min value is: "
              << d_optslv->objectiveGetValue(*min_cost.d_node) << std::endl;
  }
};