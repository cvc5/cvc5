/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of cvc5::theory::Theory.
 *
 * This test creates "fake" theory interfaces and injects them into
 * TheoryEngine, so we can test TheoryEngine's behavior without relying on
 * independent theory behavior.  This is done in TheoryEngineWhite::setUp() by
 * means of the TheoryEngineWhite::registerTheory() interface.
 */

#include <memory>
#include <string>

#include "base/check.h"
#include "context/context.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "options/options.h"
#include "smt/smt_solver.h"
#include "test_smt.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/theory_engine.h"
#include "util/integer.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace theory;
using namespace expr;
using namespace cvc5::context;
using namespace kind;
using namespace theory::bv;

namespace test {

class TestTheoryWhiteEngine : public TestSmt
{
 protected:
  void SetUp() override
  {
    TestSmt::SetUp();

    d_theoryEngine = d_slvEngine->d_smtSolver->getTheoryEngine();
    for (TheoryId id = THEORY_FIRST; id != THEORY_LAST; ++id)
    {
      delete d_theoryEngine->d_theoryOut[id];
      delete d_theoryEngine->d_theoryTable[id];
      d_theoryEngine->d_theoryOut[id] = nullptr;
      d_theoryEngine->d_theoryTable[id] = nullptr;
    }
    d_theoryEngine->addTheory<DummyTheory<THEORY_BUILTIN> >(THEORY_BUILTIN);
    d_theoryEngine->addTheory<DummyTheory<THEORY_BOOL> >(THEORY_BOOL);
    d_theoryEngine->addTheory<DummyTheory<THEORY_UF> >(THEORY_UF);
    d_theoryEngine->addTheory<DummyTheory<THEORY_ARITH> >(THEORY_ARITH);
    d_theoryEngine->addTheory<DummyTheory<THEORY_ARRAYS> >(THEORY_ARRAYS);
    d_theoryEngine->addTheory<DummyTheory<THEORY_BV> >(THEORY_BV);
  }

  TheoryEngine* d_theoryEngine;
};

TEST_F(TestTheoryWhiteEngine, rewriter_simple)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Node x = d_nodeManager->mkVar("x", d_nodeManager->integerType());
  Node y = d_nodeManager->mkVar("y", d_nodeManager->integerType());
  Node z = d_nodeManager->mkVar("z", d_nodeManager->integerType());

  // make the expression (ADD x y (MULT z 0))
  Node zero = d_nodeManager->mkConstInt(Rational("0"));
  Node zTimesZero = d_nodeManager->mkNode(MULT, z, zero);
  Node n = d_nodeManager->mkNode(ADD, x, y, zTimesZero);

  Node nExpected = n;
  Node nOut;

  // do a full rewrite; DummyTheory::preRewrite() and DummyTheory::postRewrite()
  // assert that the rewrite calls that are made match the expected sequence
  // set up above
  nOut = rr->rewrite(n);

  // assert that the rewritten node is what we expect
  ASSERT_EQ(nOut, nExpected);
}

TEST_F(TestTheoryWhiteEngine, rewriter_complex)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Node x = d_nodeManager->mkVar("x", d_nodeManager->integerType());
  Node y = d_nodeManager->mkVar("y", d_nodeManager->realType());
  TypeNode u = d_nodeManager->mkSort("U");
  Node z1 = d_nodeManager->mkVar("z1", u);
  Node z2 = d_nodeManager->mkVar("z2", u);
  Node f = d_nodeManager->mkVar(
      "f",
      d_nodeManager->mkFunctionType(d_nodeManager->integerType(),
                                    d_nodeManager->integerType()));
  Node g = d_nodeManager->mkVar(
      "g",
      d_nodeManager->mkFunctionType(d_nodeManager->realType(),
                                    d_nodeManager->integerType()));
  Node one = d_nodeManager->mkConstInt(Rational("1"));
  Node two = d_nodeManager->mkConstInt(Rational("2"));

  Node f1 = d_nodeManager->mkNode(APPLY_UF, f, one);
  Node f2 = d_nodeManager->mkNode(APPLY_UF, f, two);
  Node fx = d_nodeManager->mkNode(APPLY_UF, f, x);
  Node ffx = d_nodeManager->mkNode(APPLY_UF, f, fx);
  Node gy = d_nodeManager->mkNode(APPLY_UF, g, y);
  Node z1eqz2 = d_nodeManager->mkNode(EQUAL, z1, z2);
  Node f1eqf2 = d_nodeManager->mkNode(EQUAL, f1, f2);
  Node ffxeqgy = d_nodeManager->mkNode(EQUAL, ffx, gy);
  Node and1 = d_nodeManager->mkNode(AND, ffxeqgy, z1eqz2);
  Node ffxeqf1 = d_nodeManager->mkNode(EQUAL, ffx, f1);
  Node or1 = d_nodeManager->mkNode(OR, and1, ffxeqf1);
  // make the expression:
  // (IMPLIES (EQUAL (f 1) (f 2))
  //   (OR (AND (EQUAL (f (f x)) (g y))
  //            (EQUAL z1 z2))
  //       (EQUAL (f (f x)) (f 1))))
  Node n = d_nodeManager->mkNode(IMPLIES, f1eqf2, or1);
  Node nExpected = n;
  Node nOut;

  // do a full rewrite; DummyTheory::preRewrite() and DummyTheory::postRewrite()
  // assert that the rewrite calls that are made match the expected sequence
  // set up above
  nOut = rr->rewrite(n);

  // assert that the rewritten node is what we expect
  ASSERT_EQ(nOut, nExpected);
}

TEST_F(TestTheoryWhiteEngine, rewrite_rules)
{
  TypeNode t = d_nodeManager->mkBitVectorType(8);
  Node x = d_nodeManager->mkVar("x", t);
  Node y = d_nodeManager->mkVar("y", t);
  Node z = d_nodeManager->mkVar("z", t);

  // (x - y) * z --> (x * z) - (y * z)
  Node expr = d_nodeManager->mkNode(
      BITVECTOR_MULT, d_nodeManager->mkNode(BITVECTOR_SUB, x, y), z);
  Node result = expr;
  if (RewriteRule<MultDistrib>::applies(expr))
  {
    result = RewriteRule<MultDistrib>::apply(expr);
  }
  Node expected =
      d_nodeManager->mkNode(BITVECTOR_SUB,
                            d_nodeManager->mkNode(BITVECTOR_MULT, x, z),
                            d_nodeManager->mkNode(BITVECTOR_MULT, y, z));
  ASSERT_EQ(result, expected);

  // Try to apply MultSlice to a multiplication of two and three different
  // variables, expect different results (x * y and x * y * z should not get
  // rewritten to the same term).
  expr = d_nodeManager->mkNode(BITVECTOR_MULT, x, y, z);
  result = expr;
  Node expr2 = d_nodeManager->mkNode(BITVECTOR_MULT, x, y);
  Node result2 = expr;
  if (RewriteRule<MultSlice>::applies(expr))
  {
    result = RewriteRule<MultSlice>::apply(expr);
  }
  if (RewriteRule<MultSlice>::applies(expr2))
  {
    result2 = RewriteRule<MultSlice>::apply(expr2);
  }
  ASSERT_NE(result, result2);
}

}  // namespace test
}  // namespace cvc5::internal
