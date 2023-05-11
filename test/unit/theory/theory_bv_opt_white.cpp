/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Aina Niemetz, Michael Chang
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White-box testing for optimization module for BitVectors.
 */
#include <iostream>

#include "smt/optimization_solver.h"
#include "test_smt.h"
#include "util/bitvector.h"

namespace cvc5::internal {

using namespace theory;
using namespace smt;

namespace test {

class TestTheoryWhiteBVOpt : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("produce-assertions", "true");
    d_slvEngine->finishInit();

    d_optslv.reset(new OptimizationSolver(d_slvEngine.get()));
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
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_ULE, a, x));
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_ULE, x, b));

  d_optslv->addObjective(x, OptimizationObjective::MINIMIZE, false);

  Result r = d_optslv->checkOpt();

  ASSERT_EQ(r.getStatus(), Result::SAT);

  ASSERT_EQ(d_optslv->getValues()[0].getValue().getConst<BitVector>(),
            BitVector(32u, (uint32_t)0x3FFFFFA1));
  d_slvEngine->resetAssertions();
}

TEST_F(TestTheoryWhiteBVOpt, signed_min)
{
  Node x = d_nodeManager->mkVar(*d_BV32Type);

  Node a = d_nodeManager->mkConst(BitVector(32u, (unsigned)0x80000000));
  Node b = d_nodeManager->mkConst(BitVector(32u, 2147483647u));
  // -2147483648 <= x <= 2147483647
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, a, x));
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, x, b));

  d_optslv->addObjective(x, OptimizationObjective::MINIMIZE, true);

  Result r = d_optslv->checkOpt();

  ASSERT_EQ(r.getStatus(), Result::SAT);

  BitVector val = d_optslv->getValues()[0].getValue().getConst<BitVector>();
  std::cout << "opt value is: " << val << std::endl;

  // expect the minimum x = -1
  ASSERT_EQ(val, BitVector(32u, (uint32_t)0x80000000));
  d_slvEngine->resetAssertions();
}

TEST_F(TestTheoryWhiteBVOpt, unsigned_max)
{
  Node x = d_nodeManager->mkVar(*d_BV32Type);

  Node a = d_nodeManager->mkConst(BitVector(32u, (unsigned)1));
  Node b = d_nodeManager->mkConst(BitVector(32u, (unsigned)2));

  // If the gap is too large, it will have a performance issue!!!
  // Need binary search!
  // (unsigned)1 <= x <= (unsigned)2
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_ULE, a, x));
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_ULE, x, b));

  d_optslv->addObjective(x, OptimizationObjective::MAXIMIZE, false);

  Result r = d_optslv->checkOpt();

  ASSERT_EQ(r.getStatus(), Result::SAT);

  BitVector val = d_optslv->getValues()[0].getValue().getConst<BitVector>();
  std::cout << "opt value is: " << val << std::endl;

  ASSERT_EQ(d_optslv->getValues()[0].getValue().getConst<BitVector>(),
            BitVector(32u, 2u));
  d_slvEngine->resetAssertions();
}

TEST_F(TestTheoryWhiteBVOpt, signed_max)
{
  Node x = d_nodeManager->mkVar(*d_BV32Type);

  Node a = d_nodeManager->mkConst(BitVector(32u, (unsigned)0x80000000));
  Node b = d_nodeManager->mkConst(BitVector(32u, 10u));

  // -2147483648 <= x <= 10
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, a, x));
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, x, b));

  d_optslv->addObjective(x, OptimizationObjective::MAXIMIZE, true);

  Result r = d_optslv->checkOpt();

  ASSERT_EQ(r.getStatus(), Result::SAT);

  // expect the maxmum x =
  ASSERT_EQ(d_optslv->getValues()[0].getValue().getConst<BitVector>(),
            BitVector(32u, 10u));
  d_slvEngine->resetAssertions();
}

TEST_F(TestTheoryWhiteBVOpt, min_boundary)
{
  Node x = d_nodeManager->mkVar(*d_BV32Type);
  Node y = d_nodeManager->mkVar(*d_BV32Type);

  // x <= 18
  d_slvEngine->assertFormula(d_nodeManager->mkNode(
      kind::BITVECTOR_ULE, d_nodeManager->mkConst(BitVector(32u, 18u)), x));
  // this perturbs the solver to trigger some boundary bug
  // that existed previously
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, y, x));

  d_optslv->addObjective(x, OptimizationObjective::MINIMIZE, false);

  Result r = d_optslv->checkOpt();

  ASSERT_EQ(r.getStatus(), Result::SAT);

  // expect the maximum x = 18
  ASSERT_EQ(d_optslv->getValues()[0].getValue().getConst<BitVector>(),
            BitVector(32u, 18u));
  d_slvEngine->resetAssertions();
}

}  // namespace test
}  // namespace cvc5::internal
