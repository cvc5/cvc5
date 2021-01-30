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
    //d_optslv(nullptr)
    //d_optslv.reset(new OptimizationSolver(this));

    d_slv = new api::Solver();
    d_smt = d_slv->getSmtEngine();
    //d_nm = d_slv->getNodeManager();
    d_nm = NodeManager::currentNM();
    d_scope = new SmtScope(d_smt);
    d_optslv = new OptimizationSolver(d_smt);

    Options opts;
    d_slv->setOption("produce-assertions", "true");
    d_slv->setOption("incremental", "true");
  }
  void tearDown() override
  {
    //delete d_nm;
    delete d_optslv;
    delete d_scope;
    delete d_slv;
  }
  void testOmt()
  {
    Term ub = d_slv->mkReal(100);
    Term lb = d_slv->mkReal(0);
    Term cost = d_slv->mkConst(d_slv->getIntegerSort(), "cost");
    Term cost2 = d_slv->mkConst(d_slv->getIntegerSort(), "cost2");

    Term upb = d_slv->mkTerm(CVC4::api::Kind::GT, ub, cost);
    Term lowb = d_slv->mkTerm(CVC4::api::Kind::GT, cost, lb);
    Term upb2 = d_slv->mkTerm(CVC4::api::Kind::GT, ub, cost2);
    Term lowb2 = d_slv->mkTerm(CVC4::api::Kind::GT, cost2, lb);
    d_slv->assertFormula(upb);
    d_slv->assertFormula(lowb);
    d_slv->assertFormula(upb2);
    d_slv->assertFormula(lowb2);

    const int type = 1;
    const int type2 = 0;
    const int result = 0;
    d_optslv->activateObj(*cost.d_node, type, result);
    d_optslv->activateObj(*cost2.d_node, type2, result);

    CVC4::Result r;
    d_optslv->checkOpt(r);

    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized max value is: " << d_optslv->objectiveGetValue(*cost.d_node)
              << std::endl;
    std::cout << "Optimized min value is: " << d_optslv->objectiveGetValue(*cost2.d_node)
              << std::endl;
  }
};