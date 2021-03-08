#include <iostream>

#include "smt/optimization_solver.h"
#include "test_smt.h"

using namespace CVC4;
using namespace smt;
using namespace api;

class omt : public CxxTest::TestSuite
{
  NodeManager* d_nm;
  SmtEngine* d_smt;
  SmtScope* d_scope;
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

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(),
                     d_nm->mkConst(BitVector(32u, 2147483647u)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized value is: " << d_optslv->objectiveGetValue()
              << std::endl;
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

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(),
                     d_nm->mkConst(BitVector(32u, (unsigned)0xFFFFFFFF)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized value is: " << d_optslv->objectiveGetValue()
              << std::endl;
  }

  void testOmtBVUnsignedMax()
  {
    Sort bitvector32 = d_slv->mkBitVectorSort(32);
    Term x = d_slv->mkConst(bitvector32, "x");
    Term a = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFA1);
    Term b = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFF1);
    // if the gap is too large, it will have a performance issue!!! Need binary
    // search! (unsigned)0xFFFFFFA1 <= x <= (unsigned)0xFFFFFFFF
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_ULE, a, x));
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_ULE, x, b));

    const ObjectiveType obj_type = OBJECTIVE_MAXIMIZE;
    d_optslv->activateObj(*x.d_node, obj_type, false);

    OptResult r = d_optslv->checkOpt();

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(),
                     d_nm->mkConst(BitVector(32u, (unsigned)0xFFFFFFF1)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized value is: " << d_optslv->objectiveGetValue()
              << std::endl;
  }

  void testOmtBVUnsignedMin()
  {
    Sort bitvector32 = d_slv->mkBitVectorSort(32);
    Term x = d_slv->mkConst(bitvector32, "x");
    Term a = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFA1);
    Term b = d_slv->mkBitVector(32u, (unsigned)0xFFFFFFF1);
    // if the gap is too large, it will have a performance issue!!! Need binary
    // search! (unsigned)0xFFFFFFA1 <= x <= (unsigned)0xFFFFFFFF
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_ULE, a, x));
    d_slv->assertFormula(d_slv->mkTerm(CVC4::api::Kind::BITVECTOR_ULE, x, b));

    const ObjectiveType obj_type = OBJECTIVE_MINIMIZE;
    d_optslv->activateObj(*x.d_node, obj_type, false);

    OptResult r = d_optslv->checkOpt();

    TS_ASSERT_EQUALS(d_optslv->objectiveGetValue(),
                     d_nm->mkConst(BitVector(32u, (unsigned)0xFFFFFFA1)));
    std::cout << "Result is :" << r << std::endl;
    std::cout << "Optimized value is: " << d_optslv->objectiveGetValue()
              << std::endl;
  }
};
