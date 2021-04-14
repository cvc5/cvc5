/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Whitebox tests for theory Arithmetic.
 */

#include <list>
#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "test_smt.h"
#include "theory/arith/theory_arith.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/rational.h"

namespace cvc5 {

using namespace theory;
using namespace theory::arith;
using namespace expr;
using namespace context;
using namespace kind;
using namespace smt;

namespace test {

class TestTheoryWhiteArith : public TestSmtNoFinishInit
{
 protected:
  void SetUp() override
  {
    TestSmtNoFinishInit::SetUp();
    d_smtEngine->setOption("incremental", "false");
    d_smtEngine->finishInit();
    d_arith = static_cast<TheoryArith*>(
        d_smtEngine->getTheoryEngine()->d_theoryTable[THEORY_ARITH]);

    d_realType.reset(new TypeNode(d_nodeManager->realType()));
    d_intType.reset(new TypeNode(d_nodeManager->integerType()));
  }

  void fakeTheoryEnginePreprocess(TNode input)
  {
    Assert(input == Rewriter::rewrite(input));
    d_smtEngine->getTheoryEngine()->preRegister(input);
  }

  Theory::Effort d_level = Theory::EFFORT_FULL;
  TheoryArith* d_arith;
  std::unique_ptr<TypeNode> d_realType;
  std::unique_ptr<TypeNode> d_intType;
  const Rational d_zero = 0;
  const Rational d_one = 1;
};

TEST_F(TestTheoryWhiteArith, assert)
{
  Node x = d_nodeManager->mkVar(*d_realType);
  Node c = d_nodeManager->mkConst<Rational>(d_zero);

  Node gt = d_nodeManager->mkNode(GT, x, c);
  Node leq = Rewriter::rewrite(gt.notNode());
  fakeTheoryEnginePreprocess(leq);

  d_arith->assertFact(leq, true);

  d_arith->check(d_level);
}

TEST_F(TestTheoryWhiteArith, int_normal_form)
{
  Node x = d_nodeManager->mkVar(*d_intType);
  Node xr = d_nodeManager->mkVar(*d_realType);
  Node c0 = d_nodeManager->mkConst<Rational>(d_zero);
  Node c1 = d_nodeManager->mkConst<Rational>(d_one);
  Node c2 = d_nodeManager->mkConst<Rational>(Rational(2));

  Node geq0 = d_nodeManager->mkNode(GEQ, x, c0);
  Node geq1 = d_nodeManager->mkNode(GEQ, x, c1);
  Node geq2 = d_nodeManager->mkNode(GEQ, x, c2);

  ASSERT_EQ(Rewriter::rewrite(geq0), geq0);
  ASSERT_EQ(Rewriter::rewrite(geq1), geq1);

  Node gt0 = d_nodeManager->mkNode(GT, x, c0);
  Node gt1 = d_nodeManager->mkNode(GT, x, c1);

  ASSERT_EQ(Rewriter::rewrite(gt0), Rewriter::rewrite(geq1));
  ASSERT_EQ(Rewriter::rewrite(gt1), Rewriter::rewrite(geq2));

  Node lt0 = d_nodeManager->mkNode(LT, x, c0);
  Node lt1 = d_nodeManager->mkNode(LT, x, c1);

  ASSERT_EQ(Rewriter::rewrite(lt0), Rewriter::rewrite(geq0.notNode()));
  ASSERT_EQ(Rewriter::rewrite(lt1), Rewriter::rewrite(geq1.notNode()));

  Node leq0 = d_nodeManager->mkNode(LEQ, x, c0);
  Node leq1 = d_nodeManager->mkNode(LEQ, x, c1);

  ASSERT_EQ(Rewriter::rewrite(leq0), Rewriter::rewrite(geq1.notNode()));
  ASSERT_EQ(Rewriter::rewrite(leq1), Rewriter::rewrite(geq2.notNode()));

  // (abs x) --> (abs x)
  Node absX = d_nodeManager->mkNode(ABS, x);
  ASSERT_EQ(Rewriter::rewrite(absX), absX);

  // (exp (+ 2 + x)) --> (* (exp x) (exp 1) (exp 1))
  Node t =
      d_nodeManager->mkNode(EXPONENTIAL, d_nodeManager->mkNode(PLUS, c2, xr))
          .eqNode(c0);
  ASSERT_EQ(Rewriter::rewrite(Rewriter::rewrite(t)), Rewriter::rewrite(t));
}
}  // namespace test
}  // namespace cvc5
