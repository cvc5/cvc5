/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for theory BV.
 */

#include <cmath>
#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "test_api.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/bitvector.h"

namespace cvc5::internal {

namespace test {

class TestTheoryBlackBv : public TestApi
{
 protected:
  void test_unsigned_overflow(cvc5::Kind kind, cvc5::Kind kindo)
  {
    d_solver.setOption("incremental", "true");
    for (uint32_t w = 1; w < 8; ++w)
    {
      d_solver.push();
      Term x = d_solver.mkConst(d_solver.mkBitVectorSort(w), "x");
      Term y = d_solver.mkConst(d_solver.mkBitVectorSort(w), "y");

      Op zext = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, {w});
      Term zx = d_solver.mkTerm(zext, {x});
      Term zy = d_solver.mkTerm(zext, {y});
      Term mul = d_solver.mkTerm(kind, {zx, zy});
      Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, {2 * w - 1, w});
      Term lhs = d_solver.mkTerm(
          DISTINCT, {d_solver.mkTerm(ext, {mul}), d_solver.mkBitVector(w)});
      Term rhs = d_solver.mkTerm(kindo, {x, y});
      Term eq = d_solver.mkTerm(DISTINCT, {lhs, rhs});
      d_solver.assertFormula(eq);
      ASSERT_TRUE(d_solver.checkSat().isUnsat());
      d_solver.pop();
    }
  }

  void test_signed_overflow(cvc5::Kind kind, cvc5::Kind kindo)
  {
    d_solver.setOption("incremental", "true");
    d_solver.setOption("produce-models", "true");
    for (uint32_t w = 1; w < 8; ++w)
    {
      d_solver.push();
      Term x = d_solver.mkConst(d_solver.mkBitVectorSort(w), "x");
      Term y = d_solver.mkConst(d_solver.mkBitVectorSort(w), "y");

      Op sext = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, {w});
      Term zx = d_solver.mkTerm(sext, {x});
      Term zy = d_solver.mkTerm(sext, {y});
      Term op = d_solver.mkTerm(kind, {zx, zy});

      Term max = d_solver.mkBitVector(
          2 * w, static_cast<uint32_t>(std::pow(2, w - 1)));
      Term min = d_solver.mkTerm(BITVECTOR_NEG, {max});

      Term lhs = d_solver.mkTerm(OR,
                                 {d_solver.mkTerm(BITVECTOR_SLT, {op, min}),
                                  d_solver.mkTerm(BITVECTOR_SGE, {op, max})});
      if (kind == BITVECTOR_SDIV)
      {
        lhs = d_solver.mkTerm(
            AND,
            {d_solver.mkTerm(DISTINCT, {y, d_solver.mkBitVector(w)}), lhs});
      }
      Term rhs = d_solver.mkTerm(kindo, {x, y});
      Term eq = d_solver.mkTerm(DISTINCT, {lhs, rhs});
      d_solver.assertFormula(eq);
      if (d_solver.checkSat().isSat())
      {
        std::cout << "x: " << d_solver.getValue(x) << std::endl;
        std::cout << "y: " << d_solver.getValue(y) << std::endl;
        std::cout << "op: " << d_solver.getValue(op) << std::endl;
        std::cout << "max: " << d_solver.getValue(max) << std::endl;
        std::cout << "lhs: " << d_solver.getValue(lhs) << std::endl;
        std::cout << "rhs: " << d_solver.getValue(rhs) << std::endl;
      }
      ASSERT_TRUE(d_solver.checkSat().isUnsat());
      d_solver.pop();
    }
  }
};

TEST_F(TestTheoryBlackBv, uaddo)
{
  test_unsigned_overflow(BITVECTOR_ADD, BITVECTOR_UADDO);
}

TEST_F(TestTheoryBlackBv, saddo)
{
  test_signed_overflow(BITVECTOR_ADD, BITVECTOR_SADDO);
}

TEST_F(TestTheoryBlackBv, umulo)
{
  test_unsigned_overflow(BITVECTOR_MULT, BITVECTOR_UMULO);
}

TEST_F(TestTheoryBlackBv, smulo)
{
  test_signed_overflow(BITVECTOR_MULT, BITVECTOR_SMULO);
}

TEST_F(TestTheoryBlackBv, usubo)
{
  test_unsigned_overflow(BITVECTOR_SUB, BITVECTOR_USUBO);
}

TEST_F(TestTheoryBlackBv, ssubo)
{
  test_signed_overflow(BITVECTOR_SUB, BITVECTOR_SSUBO);
}

TEST_F(TestTheoryBlackBv, sdivo)
{
  test_signed_overflow(BITVECTOR_SDIV, BITVECTOR_SDIVO);
}

TEST_F(TestTheoryBlackBv, reg8361)
{
  Solver slv;
  slv.setLogic("QF_BV");

  Sort bvSort = slv.mkBitVectorSort(6);
  std::vector<Term> bvs;
  for (int i = 0; i < 64; i++)
  {
    bvs.push_back(slv.mkConst(bvSort));
  }

  slv.assertFormula(slv.mkTerm(DISTINCT, bvs));
  ASSERT_TRUE(slv.checkSat().isSat());
  slv.resetAssertions();

  bvs.push_back(slv.mkConst(bvSort));
  slv.assertFormula(slv.mkTerm(DISTINCT, bvs));
  ASSERT_TRUE(slv.checkSat().isUnsat());
}
}  // namespace test
}  // namespace cvc5::internal
