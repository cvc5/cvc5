/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
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
    d_solver->setOption("incremental", "true");
    for (uint32_t w = 1; w < 8; ++w)
    {
      d_solver->push();
      Term x = d_tm.mkConst(d_tm.mkBitVectorSort(w), "x");
      Term y = d_tm.mkConst(d_tm.mkBitVectorSort(w), "y");

      Op zext = d_tm.mkOp(cvc5::Kind::BITVECTOR_ZERO_EXTEND, {w});
      Term zx = d_tm.mkTerm(zext, {x});
      Term zy = d_tm.mkTerm(zext, {y});
      Term op = d_tm.mkTerm(kind, {zx, zy});
      Op ext = d_tm.mkOp(cvc5::Kind::BITVECTOR_EXTRACT, {2 * w - 1, w});
      Term lhs = d_tm.mkTerm(cvc5::Kind::DISTINCT,
                             {d_tm.mkTerm(ext, {op}), d_tm.mkBitVector(w)});
      Term rhs = d_tm.mkTerm(kindo, {x, y});
      Term eq = d_tm.mkTerm(cvc5::Kind::DISTINCT, {lhs, rhs});
      d_solver->assertFormula(eq);
      ASSERT_TRUE(d_solver->checkSat().isUnsat());
      d_solver->pop();
    }
  }

  void test_signed_overflow(cvc5::Kind kind, cvc5::Kind kindo)
  {
    d_solver->setOption("incremental", "true");
    d_solver->setOption("produce-models", "true");
    for (uint32_t w = 1; w < 8; ++w)
    {
      d_solver->push();
      Term x = d_tm.mkConst(d_tm.mkBitVectorSort(w), "x");
      Term y = d_tm.mkConst(d_tm.mkBitVectorSort(w), "y");

      Op sext = d_tm.mkOp(cvc5::Kind::BITVECTOR_SIGN_EXTEND, {w});
      Term zx = d_tm.mkTerm(sext, {x});
      Term zy = d_tm.mkTerm(sext, {y});
      Term op = d_tm.mkTerm(kind, {zx, zy});

      Term max =
          d_tm.mkBitVector(2 * w, static_cast<uint32_t>(std::pow(2, w - 1)));
      Term min = d_tm.mkTerm(cvc5::Kind::BITVECTOR_NEG, {max});

      Term lhs =
          d_tm.mkTerm(cvc5::Kind::OR,
                      {d_tm.mkTerm(cvc5::Kind::BITVECTOR_SLT, {op, min}),
                       d_tm.mkTerm(cvc5::Kind::BITVECTOR_SGE, {op, max})});
      if (kind == cvc5::Kind::BITVECTOR_SDIV)
      {
        lhs = d_tm.mkTerm(
            cvc5::Kind::AND,
            {d_tm.mkTerm(cvc5::Kind::DISTINCT, {y, d_tm.mkBitVector(w)}), lhs});
      }
      Term rhs = d_tm.mkTerm(kindo, {x, y});
      Term eq = d_tm.mkTerm(cvc5::Kind::DISTINCT, {lhs, rhs});
      d_solver->assertFormula(eq);
      ASSERT_TRUE(d_solver->checkSat().isUnsat());
      d_solver->pop();
    }
  }
};

TEST_F(TestTheoryBlackBv, nego)
{
  d_solver->setOption("incremental", "true");
  d_solver->setOption("produce-models", "true");
  for (uint32_t w = 1; w < 8; ++w)
  {
    d_solver->push();
    Term one = d_tm.mkBitVector(2 * w, 1);
    Term x = d_tm.mkConst(d_tm.mkBitVectorSort(w), "x");
    Term lhs = d_tm.mkTerm(
        cvc5::Kind::EQUAL,
        {x,
         d_tm.mkTerm(cvc5::Kind::BITVECTOR_SHL,
                     {d_tm.mkBitVector(w, 1), d_tm.mkBitVector(w, w - 1)})});
    Term rhs = d_tm.mkTerm(cvc5::Kind::BITVECTOR_NEGO, {x});
    Term eq = d_tm.mkTerm(cvc5::Kind::DISTINCT, {lhs, rhs});
    d_solver->assertFormula(eq);
    ASSERT_TRUE(d_solver->checkSat().isUnsat());
    d_solver->pop();
  }
}

TEST_F(TestTheoryBlackBv, uaddo)
{
  test_unsigned_overflow(cvc5::Kind::BITVECTOR_ADD,
                         cvc5::Kind::BITVECTOR_UADDO);
}

TEST_F(TestTheoryBlackBv, saddo)
{
  test_signed_overflow(cvc5::Kind::BITVECTOR_ADD, cvc5::Kind::BITVECTOR_SADDO);
}

TEST_F(TestTheoryBlackBv, umulo)
{
  test_unsigned_overflow(cvc5::Kind::BITVECTOR_MULT,
                         cvc5::Kind::BITVECTOR_UMULO);
}

TEST_F(TestTheoryBlackBv, smulo)
{
  test_signed_overflow(cvc5::Kind::BITVECTOR_MULT, cvc5::Kind::BITVECTOR_SMULO);
}

TEST_F(TestTheoryBlackBv, usubo)
{
  test_unsigned_overflow(cvc5::Kind::BITVECTOR_SUB,
                         cvc5::Kind::BITVECTOR_USUBO);
}

TEST_F(TestTheoryBlackBv, ssubo)
{
  test_signed_overflow(cvc5::Kind::BITVECTOR_SUB, cvc5::Kind::BITVECTOR_SSUBO);
}

TEST_F(TestTheoryBlackBv, sdivo)
{
  test_signed_overflow(cvc5::Kind::BITVECTOR_SDIV, cvc5::Kind::BITVECTOR_SDIVO);
}

TEST_F(TestTheoryBlackBv, reg8361)
{
  Solver slv(d_tm);
  slv.setLogic("QF_BV");

  Sort bvSort = d_tm.mkBitVectorSort(6);
  std::vector<Term> bvs;
  for (int i = 0; i < 64; i++)
  {
    bvs.push_back(d_tm.mkConst(bvSort));
  }

  slv.assertFormula(d_tm.mkTerm(cvc5::Kind::DISTINCT, bvs));
  ASSERT_TRUE(slv.checkSat().isSat());
  slv.resetAssertions();

  bvs.push_back(d_tm.mkConst(bvSort));
  slv.assertFormula(d_tm.mkTerm(cvc5::Kind::DISTINCT, bvs));
  ASSERT_TRUE(slv.checkSat().isUnsat());
}
}  // namespace test
}  // namespace cvc5::internal
