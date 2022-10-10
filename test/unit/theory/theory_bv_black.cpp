/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
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
};

TEST_F(TestTheoryBlackBv, uaddo)
{
  d_solver.setOption("incremental", "true");
  for (uint32_t w = 1; w < 8; ++w)
  {
    d_solver.push();
    Term x = d_solver.mkConst(d_solver.mkBitVectorSort(w), "x");
    Term y = d_solver.mkConst(d_solver.mkBitVectorSort(w), "y");

    Op zext = d_solver.mkOp(BITVECTOR_ZERO_EXTEND, {1});
    Term zx = d_solver.mkTerm(zext, {x});
    Term zy = d_solver.mkTerm(zext, {y});
    Term add = d_solver.mkTerm(BITVECTOR_ADD, {zx, zy});
    Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, {w, w});
    Term lhs = d_solver.mkTerm(
        DISTINCT, {d_solver.mkTerm(ext, {add}), d_solver.mkBitVector(1)});
    Term rhs = d_solver.mkTerm(BITVECTOR_UADDO, {x, y});
    Term eq = d_solver.mkTerm(DISTINCT, {lhs, rhs});
    d_solver.assertFormula(eq);
    ASSERT_TRUE(d_solver.checkSat().isUnsat());
    d_solver.pop();
  }
}

TEST_F(TestTheoryBlackBv, umulo)
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
    Term mul = d_solver.mkTerm(BITVECTOR_MULT, {zx, zy});
    Op ext = d_solver.mkOp(BITVECTOR_EXTRACT, {2 * w - 1, w});
    Term lhs = d_solver.mkTerm(
        DISTINCT, {d_solver.mkTerm(ext, {mul}), d_solver.mkBitVector(w)});
    Term rhs = d_solver.mkTerm(BITVECTOR_UMULO, {x, y});
    Term eq = d_solver.mkTerm(DISTINCT, {lhs, rhs});
    d_solver.assertFormula(eq);
    ASSERT_TRUE(d_solver.checkSat().isUnsat());
    d_solver.pop();
  }
}

TEST_F(TestTheoryBlackBv, smulo)
{
  d_solver.setOption("incremental", "true");
  for (uint32_t w = 1; w < 8; ++w)
  {
    d_solver.push();
    Term x = d_solver.mkConst(d_solver.mkBitVectorSort(w), "x");
    Term y = d_solver.mkConst(d_solver.mkBitVectorSort(w), "y");

    Op sext = d_solver.mkOp(BITVECTOR_SIGN_EXTEND, {w});
    Term zx = d_solver.mkTerm(sext, {x});
    Term zy = d_solver.mkTerm(sext, {y});
    Term mul = d_solver.mkTerm(BITVECTOR_MULT, {zx, zy});

    Term max =
        d_solver.mkBitVector(2 * w, static_cast<uint32_t>(std::pow(2, w - 1)));
    Term min = d_solver.mkTerm(BITVECTOR_NEG, {max});

    Term lhs = d_solver.mkTerm(OR,
                               {d_solver.mkTerm(BITVECTOR_SLT, {mul, min}),
                                d_solver.mkTerm(BITVECTOR_SGE, {mul, max})});
    Term rhs = d_solver.mkTerm(BITVECTOR_SMULO, {x, y});
    Term eq = d_solver.mkTerm(DISTINCT, {lhs, rhs});
    d_solver.assertFormula(eq);
    ASSERT_TRUE(d_solver.checkSat().isUnsat());
    d_solver.pop();
  }
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
