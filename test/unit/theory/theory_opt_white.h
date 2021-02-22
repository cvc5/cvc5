#include <iostream>
#include <cxxtest/TestSuite.h>
#include "api/cvc4cpp.h"
#include "smt/opt_solver.h"
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

  void testOmtOpen()
  {
    Term ub1 = d_slv->mkInteger(100);
    Term lb1 = d_slv->mkInteger(0);
    Term lb2 = d_slv->mkInteger(110);

    Term cost1 = d_slv->mkConst(d_slv->getIntegerSort(), "cost3"); 
    Term cost2 = d_slv->mkConst(d_slv->getIntegerSort(), "cost4");
    // 0 < cost1 < 100
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LT, lb1, cost1));
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LT, cost1, ub1));
    // 110 < cost2
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LT, lb2, cost2));

    Term cost3 = d_slv->mkTerm(CVC4::api::PLUS, cost1, cost2);

    const ObjectiveType min_type = OBJECTIVE_MINIMIZE;
    d_optslv->activateObj(*cost3.d_node, min_type);

    OptResult r = d_optslv->checkOpt();

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(), d_nm->mkConst(Rational(112)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized min value is: " << d_optslv->objectiveGetValue() << std::endl;
  }

  void testOmtOpenReal()
  {
    // WARNING: domain is infinite, though it's bounded, it's still possible not run to completion! 
    Term ub1 = d_slv->mkReal(100);
    Term lb1 = d_slv->mkReal(0);
    Term lb2 = d_slv->mkReal(110);
    Term ub2 = d_slv->mkReal(120);

    Term cost1 = d_slv->mkConst(d_slv->getRealSort(), "cost3"); 
    Term cost2 = d_slv->mkConst(d_slv->getRealSort(), "cost4");
    // 0 <= cost1 <= 100
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LEQ, lb1, cost1));
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LEQ, cost1, ub1));
    // 110 <= cost2 <= 120
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LEQ, lb2, cost2));
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::LEQ, cost2, ub2));

    Term cost3 = d_slv->mkTerm(CVC4::api::PLUS, cost1, cost2);

    const ObjectiveType obj_type = OBJECTIVE_MINIMIZE;
    d_optslv->activateObj(*cost3.d_node, obj_type);

    OptResult r = d_optslv->checkOpt();

    // TS_ASSERT_EQUALS(ub1, ub2);

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(), d_nm->mkConst(Rational(110)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized value is: " << d_optslv->objectiveGetValue() << std::endl;
  }

  void testOmtBVSignedMax()
  {
    Sort bitvector32 = d_slv->mkBitVectorSort(32);
    Term x = d_slv->mkConst(bitvector32, "x");
    Term a = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFFF);
    Term b = d_slv->mkBitVector(32u, 2147483647u);
    // 0 <= x <= 2147483647
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_SLE, a, x));
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_SLE, x, b));

    const ObjectiveType obj_type = OBJECTIVE_MAXIMIZE;
    d_optslv->activateObj(*x.d_node, obj_type, true);

    OptResult r = d_optslv->checkOpt();

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(), d_nm->mkConst(BitVector(32u, 2147483647u)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized value is: " << d_optslv->objectiveGetValue() << std::endl;
  } 

  void testOmtBVSignedMin()
  {
    Sort bitvector32 = d_slv->mkBitVectorSort(32);
    Term x = d_slv->mkConst(bitvector32, "x");
    Term a = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFFF);
    Term b = d_slv->mkBitVector(32u, 2147483647u);
    // -1 <= x <= 2147483647
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_SLE, a, x));
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_SLE, x, b));

    const ObjectiveType obj_type = OBJECTIVE_MINIMIZE;
    d_optslv->activateObj(*x.d_node, obj_type, true);

    OptResult r = d_optslv->checkOpt();

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(), d_nm->mkConst(BitVector(32u, (unsigned)0xFFFFFFFF)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized value is: " << d_optslv->objectiveGetValue() << std::endl;
  }

  void testOmtBVUnsignedMax()
  {
    Sort bitvector32 = d_slv->mkBitVectorSort(32);
    Term x = d_slv->mkConst(bitvector32, "x");
    Term a = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFA1);  
    Term b = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFF1);
    // if the gap is too large, it will have a performance issue!!! Need binary search! 
    // (unsigned)0xFFFFFFA1 <= x <= (unsigned)0xFFFFFFFF
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_ULE, a, x));
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_ULE, x, b));

    const ObjectiveType obj_type = OBJECTIVE_MAXIMIZE;
    d_optslv->activateObj(*x.d_node, obj_type, false);

    OptResult r = d_optslv->checkOpt();

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(), d_nm->mkConst(BitVector(32u, (unsigned)0xFFFFFFF1)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized value is: " << d_optslv->objectiveGetValue() << std::endl;
  }

  void testOmtBVUnsignedMin()
  {
    Sort bitvector32 = d_slv->mkBitVectorSort(32);
    Term x = d_slv->mkConst(bitvector32, "x");
    Term a = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFA1);  
    Term b = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFF1);
    // if the gap is too large, it will have a performance issue!!! Need binary search! 
    // (unsigned)0xFFFFFFA1 <= x <= (unsigned)0xFFFFFFFF
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_ULE, a, x));
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_ULE, x, b));

    const ObjectiveType obj_type = OBJECTIVE_MINIMIZE;
    d_optslv->activateObj(*x.d_node, obj_type, false);

    OptResult r = d_optslv->checkOpt();

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(), d_nm->mkConst(BitVector(32u, (unsigned)0xFFFFFFA1)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized value is: " << d_optslv->objectiveGetValue() << std::endl;
  }

  // void testOmtString()
  // {
  //   Term str1 = d_slv->mkString("test1");
  //   Term str2 = d_slv->mkString("test99");
  //   Term base_str = d_slv->mkString("test");
  //   Term target_str = d_slv->mkConst(d_slv->getStringSort(), "target");

  //   // test9 < test+x < test99
  //   // x = 98 ?
  //   Term concat = d_slv->mkTerm(CVC4::api::Kind::STRING_CONCAT, base_str, target_str);
  //   d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::STRING_LT, str1, concat));
  //   d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::STRING_LT, concat, str2));

  //   const ObjectiveType obj_type = OBJECTIVE_MINIMIZE;
  //   d_optslv->activateObj(*target_str.d_node, obj_type);

  //   OptResult r = d_optslv->checkOpt();

  //   TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(), d_nm->mkConst(String("98")));
  //   std::cout << "Result is :" << r << std::endl;
  //   std::cout << "Optimized value is: " << d_optslv->objectiveGetValue() << std::endl;
  // }
};

