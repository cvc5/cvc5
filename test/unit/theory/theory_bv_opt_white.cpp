/*********************                                                        */
/*! \file theory_bv_opt_white.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yancheng Ou
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White-box testing for optimization module for BitVectors.
 **/
#include <iostream>

#include "smt/optimization_solver.h"
#include "test_smt.h"

namespace cvc5 {

using namespace theory;
using namespace smt;

namespace test {

class TestTheoryWhiteBVOpt : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_smtEngine->setOption("produce-assertions", "true");
    d_smtEngine->finishInit();

    d_optslv.reset(new OptimizationSolver(d_smtEngine.get()));
    d_BV32Type.reset(new TypeNode(d_nodeManager->mkBitVectorType(32u)));
    d_BV16Type.reset(new TypeNode(d_nodeManager->mkBitVectorType(16u)));
  }

  std::unique_ptr<OptimizationSolver> d_optslv;
  std::unique_ptr<TypeNode> d_BV32Type;
  std::unique_ptr<TypeNode> d_BV16Type;
};

TEST_F(TestTheoryWhiteBVOpt, unsigned_min)
{
  Node x = d_nodeManager->mkVar(*d_BV32Type);

  Node a = d_nodeManager->mkConst(BitVector(32u, (unsigned)0x3FFFFFA1));
  Node b = d_nodeManager->mkConst(BitVector(32u, (unsigned)0xFFFFFFF1));

  // (unsigned)0x3FFFFFA1 <= x <= (unsigned)0xFFFFFFF1
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_ULE, a, x));
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_ULE, x, b));

  const ObjectiveType obj_type = ObjectiveType::OBJECTIVE_MINIMIZE;
  d_optslv->activateObj(x, obj_type, false);

  OptResult r = d_optslv->checkOpt();

  ASSERT_EQ(r, OptResult::OPT_OPTIMAL);

  ASSERT_EQ(d_optslv->objectiveGetValue(),
            d_nodeManager->mkConst(BitVector(32u, (unsigned)0x3FFFFFA1)));

  std::cout << "Passed!" << std::endl;
  std::cout << "Optimized value is: " << d_optslv->objectiveGetValue()
            << std::endl;
}

TEST_F(TestTheoryWhiteBVOpt, signed_min)
{
  Node x = d_nodeManager->mkVar(*d_BV32Type);

  Node a = d_nodeManager->mkConst(BitVector(32u, (unsigned)0x80000000));
  Node b = d_nodeManager->mkConst(BitVector(32u, 2147483647u));
  // -2147483648 <= x <= 2147483647
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, a, x));
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, x, b));

  const ObjectiveType obj_type = ObjectiveType::OBJECTIVE_MINIMIZE;
  d_optslv->activateObj(x, obj_type, true);

  OptResult r = d_optslv->checkOpt();

  ASSERT_EQ(r, OptResult::OPT_OPTIMAL);

  BitVector val = d_optslv->objectiveGetValue().getConst<BitVector>();
  std::cout << "opt value is: " << val << std::endl;

  // expect the minimum x = -1
  ASSERT_EQ(d_optslv->objectiveGetValue(),
            d_nodeManager->mkConst(BitVector(32u, (unsigned)0x80000000)));
  std::cout << "Passed!" << std::endl;
  std::cout << "Optimized value is: " << d_optslv->objectiveGetValue()
            << std::endl;
}

TEST_F(TestTheoryWhiteBVOpt, unsigned_max)
{
  Node x = d_nodeManager->mkVar(*d_BV32Type);

  Node a = d_nodeManager->mkConst(BitVector(32u, (unsigned)1));
  Node b = d_nodeManager->mkConst(BitVector(32u, (unsigned)2));

  // If the gap is too large, it will have a performance issue!!!
  // Need binary search!
  // (unsigned)1 <= x <= (unsigned)2
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_ULE, a, x));
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_ULE, x, b));

  const ObjectiveType obj_type = ObjectiveType::OBJECTIVE_MAXIMIZE;
  d_optslv->activateObj(x, obj_type, false);

  OptResult r = d_optslv->checkOpt();

  ASSERT_EQ(r, OptResult::OPT_OPTIMAL);

  BitVector val = d_optslv->objectiveGetValue().getConst<BitVector>();
  std::cout << "opt value is: " << val << std::endl;

  ASSERT_EQ(d_optslv->objectiveGetValue(),
            d_nodeManager->mkConst(BitVector(32u, (unsigned)2)));
  std::cout << "Optimized value is: " << d_optslv->objectiveGetValue()
            << std::endl;
}

TEST_F(TestTheoryWhiteBVOpt, signed_max)
{
  Node x = d_nodeManager->mkVar(*d_BV32Type);

  Node a = d_nodeManager->mkConst(BitVector(32u, (unsigned)0x80000000));
  Node b = d_nodeManager->mkConst(BitVector(32u, 10u));

  // -2147483648 <= x <= 10
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, a, x));
  d_smtEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, x, b));

  const ObjectiveType obj_type = ObjectiveType::OBJECTIVE_MAXIMIZE;
  d_optslv->activateObj(x, obj_type, true);

  OptResult r = d_optslv->checkOpt();

  ASSERT_EQ(r, OptResult::OPT_OPTIMAL);

  // expect the maxmum x =
  ASSERT_EQ(d_optslv->objectiveGetValue(),
            d_nodeManager->mkConst(BitVector(32u, 10u)));
  std::cout << "Optimized value is: " << d_optslv->objectiveGetValue()
            << std::endl;
}

}  // namespace test
}  // namespace cvc5
