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
  void testOmtMax()
  {
    Term ub = d_slv->mkReal(100);
    Term lb = d_slv->mkReal(0);

    // Objectives to be optimized max_cost is max objective
    Term max_cost = d_slv->mkConst(d_slv->getIntegerSort(), "cost");

    Term upb = d_slv->mkTerm(CVC4::api::Kind::GT, ub, max_cost);
    Term lowb = d_slv->mkTerm(CVC4::api::Kind::GT, max_cost, lb);

    /* Result of asserts is:
       0 < max_cost < 100
    */
    d_slv->assertFormula(upb);
    d_slv->assertFormula(lowb);

    const ObjectiveType max_type = OBJECTIVE_MAXIMIZE;

    // We activate our objective so the subsolver knows to optimize it
    d_optslv->activateObj(*max_cost.d_node, max_type);

    OptResult r = d_optslv->checkOpt();

    // We expect max_cost == 99
    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(),
                     d_nm->mkConst(Rational(99)));

    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized max value is: "
              << d_optslv->objectiveGetValue() << std::endl;
  }
  void testOmtMin()
  {
    Term ub = d_slv->mkReal(100);
    Term lb = d_slv->mkReal(0);

    // Objectives to be optimized max_cost is max objective min_cost is min
    // objective

    Term min_cost = d_slv->mkConst(d_slv->getIntegerSort(), "cost2");

    Term upb2 = d_slv->mkTerm(CVC4::api::Kind::GT, ub, min_cost);
    Term lowb2 = d_slv->mkTerm(CVC4::api::Kind::GT, min_cost, lb);

    /* Result of asserts is:
       0 < max_cost < 100
       0 < min_cost < 100
    */
    d_slv->assertFormula(upb2);
    d_slv->assertFormula(lowb2);

    const ObjectiveType min_type = OBJECTIVE_MINIMIZE;

    // We activate our objective so the subsolver knows to optimize it
    d_optslv->activateObj(*min_cost.d_node, min_type);

    OptResult r = d_optslv->checkOpt();

    // We expect min_cost == 1
    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(),
                     d_nm->mkConst(Rational(1)));

    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized min value is: "
              << d_optslv->objectiveGetValue() << std::endl;
  }
  void testOmtResult()
  {
    Term ub = d_slv->mkReal(100);
    Term lb = d_slv->mkReal(0);

    // Objectives to be optimized mmin_cost is min objective

    Term min_cost = d_slv->mkConst(d_slv->getIntegerSort(), "cost2");

    Term upb2 = d_slv->mkTerm(CVC4::api::Kind::GT, lb, min_cost);
    Term lowb2 = d_slv->mkTerm(CVC4::api::Kind::GT, min_cost, ub);

    /* Result of asserts is:
       0 > min_cost >100
    */
    d_slv->assertFormula(upb2);
    d_slv->assertFormula(lowb2);

    const ObjectiveType min_type = OBJECTIVE_MINIMIZE;

    // We activate our objective so the subsolver knows to optimize it
    d_optslv->activateObj(*min_cost.d_node, min_type);

    // This should return OPT_UNSAT since 0 > x > 100 is impossible.
    OptResult r = d_optslv->checkOpt();

    TS_ASSERT_EQUALS(r, OPT_UNSAT);

    std::cout << "Result is :" << r << std::endl;
  }
};
