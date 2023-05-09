/******************************************************************************
 * Top contributors (to current version):
 *   Yancheng Ou, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White-box testing for multigoal optimization.
 */
#include <iostream>

#include "smt/optimization_solver.h"
#include "test_smt.h"
#include "util/bitvector.h"

namespace cvc5::internal {

using namespace theory;
using namespace smt;

namespace test {

class TestTheoryWhiteOptMultigoal : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_slvEngine->setOption("produce-assertions", "true");
    d_slvEngine->finishInit();

    d_BV32Type.reset(new TypeNode(d_nodeManager->mkBitVectorType(32u)));
  }

  std::unique_ptr<TypeNode> d_BV32Type;
};

TEST_F(TestTheoryWhiteOptMultigoal, box)
{
  d_slvEngine->resetAssertions();
  Node x = d_nodeManager->mkVar(*d_BV32Type);
  Node y = d_nodeManager->mkVar(*d_BV32Type);
  Node z = d_nodeManager->mkVar(*d_BV32Type);

  // 18 <= x
  d_slvEngine->assertFormula(d_nodeManager->mkNode(
      kind::BITVECTOR_ULE, d_nodeManager->mkConst(BitVector(32u, 18u)), x));

  // y <= x
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, y, x));

  OptimizationSolver optSolver(d_slvEngine.get());

  // minimize x
  optSolver.addObjective(x, OptimizationObjective::MINIMIZE, false);
  // maximize y with `signed` comparison over bit-vectors.
  optSolver.addObjective(y, OptimizationObjective::MAXIMIZE, true);
  // maximize z
  optSolver.addObjective(z, OptimizationObjective::MAXIMIZE, false);

  // Box optimization
  Result r = optSolver.checkOpt(OptimizationSolver::BOX);

  ASSERT_EQ(r.getStatus(), Result::SAT);

  std::vector<OptimizationResult> results = optSolver.getValues();

  // x == 18
  ASSERT_EQ(results[0].getValue().getConst<BitVector>(), BitVector(32u, 18u));

  // y == 0x7FFFFFFF
  ASSERT_EQ(results[1].getValue().getConst<BitVector>(),
            BitVector(32u, (unsigned)0x7FFFFFFF));

  // z == 0xFFFFFFFF
  ASSERT_EQ(results[2].getValue().getConst<BitVector>(),
            BitVector(32u, (unsigned)0xFFFFFFFF));
}

TEST_F(TestTheoryWhiteOptMultigoal, lex)
{
  d_slvEngine->resetAssertions();
  Node x = d_nodeManager->mkVar(*d_BV32Type);
  Node y = d_nodeManager->mkVar(*d_BV32Type);
  Node z = d_nodeManager->mkVar(*d_BV32Type);

  // 18 <= x
  d_slvEngine->assertFormula(d_nodeManager->mkNode(
      kind::BITVECTOR_ULE, d_nodeManager->mkConst(BitVector(32u, 18u)), x));

  // y <= x
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, y, x));

  OptimizationSolver optSolver(d_slvEngine.get());

  // minimize x
  optSolver.addObjective(x, OptimizationObjective::MINIMIZE, false);
  // maximize y with `signed` comparison over bit-vectors.
  optSolver.addObjective(y, OptimizationObjective::MAXIMIZE, true);
  // maximize z
  optSolver.addObjective(z, OptimizationObjective::MAXIMIZE, false);

  Result r = optSolver.checkOpt(OptimizationSolver::LEXICOGRAPHIC);

  ASSERT_EQ(r.getStatus(), Result::SAT);

  std::vector<OptimizationResult> results = optSolver.getValues();

  // x == 18
  ASSERT_EQ(results[0].getValue().getConst<BitVector>(), BitVector(32u, 18u));

  // y == 18
  ASSERT_EQ(results[1].getValue().getConst<BitVector>(), BitVector(32u, 18u));

  // z == 0xFFFFFFFF
  ASSERT_EQ(results[2].getValue().getConst<BitVector>(),
            BitVector(32u, (unsigned)0xFFFFFFFF));
}

TEST_F(TestTheoryWhiteOptMultigoal, pareto)
{
  d_slvEngine->resetAssertions();
  TypeNode bv4ty(d_nodeManager->mkBitVectorType(4u));
  Node a = d_nodeManager->mkVar(bv4ty);
  Node b = d_nodeManager->mkVar(bv4ty);

  Node bv1 = d_nodeManager->mkConst(BitVector(4u, 1u));
  Node bv2 = d_nodeManager->mkConst(BitVector(4u, 2u));
  Node bv3 = d_nodeManager->mkConst(BitVector(4u, 3u));

  std::vector<Node> stmts = {
      // (and (= a 1) (= b 1))
      d_nodeManager->mkNode(kind::AND,
                            d_nodeManager->mkNode(kind::EQUAL, a, bv1),
                            d_nodeManager->mkNode(kind::EQUAL, b, bv1)),
      // (and (= a 2) (= b 1))
      d_nodeManager->mkNode(kind::AND,
                            d_nodeManager->mkNode(kind::EQUAL, a, bv2),
                            d_nodeManager->mkNode(kind::EQUAL, b, bv1)),
      // (and (= a 1) (= b 2))
      d_nodeManager->mkNode(kind::AND,
                            d_nodeManager->mkNode(kind::EQUAL, a, bv1),
                            d_nodeManager->mkNode(kind::EQUAL, b, bv2)),
      // (and (= a 2) (= b 2))
      d_nodeManager->mkNode(kind::AND,
                            d_nodeManager->mkNode(kind::EQUAL, a, bv2),
                            d_nodeManager->mkNode(kind::EQUAL, b, bv2)),
      // (and (= a 3) (= b 1))
      d_nodeManager->mkNode(kind::AND,
                            d_nodeManager->mkNode(kind::EQUAL, a, bv3),
                            d_nodeManager->mkNode(kind::EQUAL, b, bv1)),
      // (and (= a 1) (= b 3))
      d_nodeManager->mkNode(kind::AND,
                            d_nodeManager->mkNode(kind::EQUAL, a, bv1),
                            d_nodeManager->mkNode(kind::EQUAL, b, bv3)),
  };
  /*
  (assert (or
    (and (= a 1) (= b 1))
    (and (= a 2) (= b 1))
    (and (= a 1) (= b 2))
    (and (= a 2) (= b 2))
    (and (= a 3) (= b 1))
    (and (= a 1) (= b 3))
  ))
  */
  d_slvEngine->assertFormula(d_nodeManager->mkOr(stmts));

  /*
    (maximize a)
    (maximize b)
   */
  OptimizationSolver optSolver(d_slvEngine.get());
  optSolver.addObjective(a, OptimizationObjective::MAXIMIZE);
  optSolver.addObjective(b, OptimizationObjective::MAXIMIZE);

  Result r;

  // all possible result pairs <a, b>
  std::set<std::pair<uint32_t, uint32_t>> possibleResults = {
      {1, 3}, {2, 2}, {3, 1}};

  r = optSolver.checkOpt(OptimizationSolver::PARETO);
  ASSERT_EQ(r.getStatus(), Result::SAT);
  std::vector<OptimizationResult> results = optSolver.getValues();
  std::pair<uint32_t, uint32_t> res = {
      results[0].getValue().getConst<BitVector>().toInteger().toUnsignedInt(),
      results[1].getValue().getConst<BitVector>().toInteger().toUnsignedInt()};
  for (auto& rn : results)
  {
    std::cout << rn.getValue().getConst<BitVector>().toInteger().toUnsignedInt()
              << " ";
  }
  std::cout << std::endl;
  ASSERT_EQ(possibleResults.count(res), 1);
  possibleResults.erase(res);

  r = optSolver.checkOpt(OptimizationSolver::PARETO);
  ASSERT_EQ(r.getStatus(), Result::SAT);
  results = optSolver.getValues();
  res = {
      results[0].getValue().getConst<BitVector>().toInteger().toUnsignedInt(),
      results[1].getValue().getConst<BitVector>().toInteger().toUnsignedInt()};
  for (auto& rn : results)
  {
    std::cout << rn.getValue().getConst<BitVector>().toInteger().toUnsignedInt()
              << " ";
  }
  std::cout << std::endl;
  ASSERT_EQ(possibleResults.count(res), 1);
  possibleResults.erase(res);

  r = optSolver.checkOpt(OptimizationSolver::PARETO);
  ASSERT_EQ(r.getStatus(), Result::SAT);
  results = optSolver.getValues();
  res = {
      results[0].getValue().getConst<BitVector>().toInteger().toUnsignedInt(),
      results[1].getValue().getConst<BitVector>().toInteger().toUnsignedInt()};
  for (auto& rn : results)
  {
    std::cout << rn.getValue().getConst<BitVector>().toInteger().toUnsignedInt()
              << " ";
  }
  std::cout << std::endl;
  ASSERT_EQ(possibleResults.count(res), 1);
  possibleResults.erase(res);

  r = optSolver.checkOpt(OptimizationSolver::PARETO);
  ASSERT_EQ(r.getStatus(), Result::UNSAT);
  ASSERT_EQ(possibleResults.size(), 0);
}

TEST_F(TestTheoryWhiteOptMultigoal, pushpop)
{
  d_slvEngine->resetAssertions();
  Node x = d_nodeManager->mkVar(*d_BV32Type);
  Node y = d_nodeManager->mkVar(*d_BV32Type);
  Node z = d_nodeManager->mkVar(*d_BV32Type);

  // 18 <= x
  d_slvEngine->assertFormula(d_nodeManager->mkNode(
      kind::BITVECTOR_ULE, d_nodeManager->mkConst(BitVector(32u, 18u)), x));

  // y <= x
  d_slvEngine->assertFormula(d_nodeManager->mkNode(kind::BITVECTOR_SLE, y, x));

  OptimizationSolver optSolver(d_slvEngine.get());

  // minimize x
  optSolver.addObjective(x, OptimizationObjective::MINIMIZE, false);

  // push
  d_slvEngine->push();

  // maximize y with `signed` comparison over bit-vectors.
  optSolver.addObjective(y, OptimizationObjective::MAXIMIZE, true);
  // maximize z
  optSolver.addObjective(z, OptimizationObjective::MAXIMIZE, false);

  // Lexico optimization
  Result r = optSolver.checkOpt(OptimizationSolver::LEXICOGRAPHIC);

  ASSERT_EQ(r.getStatus(), Result::SAT);

  std::vector<OptimizationResult> results = optSolver.getValues();

  // x == 18
  ASSERT_EQ(results[0].getValue().getConst<BitVector>(), BitVector(32u, 18u));

  // y == 18
  ASSERT_EQ(results[1].getValue().getConst<BitVector>(), BitVector(32u, 18u));

  // z == 0xFFFFFFFF
  ASSERT_EQ(results[2].getValue().getConst<BitVector>(),
            BitVector(32u, (unsigned)0xFFFFFFFF));

  // pop
  d_slvEngine->pop();

  // now we only have one objective: (minimize x)
  r = optSolver.checkOpt(OptimizationSolver::LEXICOGRAPHIC);
  ASSERT_EQ(r.getStatus(), Result::SAT);
  results = optSolver.getValues();
  ASSERT_EQ(results.size(), 1);
  ASSERT_EQ(results[0].getValue().getConst<BitVector>(), BitVector(32u, 18u));

  // resetting the assertions also resets the optimization objectives
  d_slvEngine->resetAssertions();
  r = optSolver.checkOpt(OptimizationSolver::LEXICOGRAPHIC);
  ASSERT_EQ(r.getStatus(), Result::SAT);
  results = optSolver.getValues();
  ASSERT_EQ(results.size(), 0);
}

}  // namespace test
}  // namespace cvc5::internal
