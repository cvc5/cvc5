/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include "smt/smt_solver.h"
#include "test_smt.h"
#include "theory/arith/theory_arith.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory.h"
#include "theory/theory_engine.h"
#include "util/rational.h"

namespace cvc5::internal {

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
    d_slvEngine->setOption("incremental", "false");
    d_slvEngine->finishInit();
    TheoryEngine* te = d_slvEngine->d_smtSolver->getTheoryEngine();
    d_arith = static_cast<TheoryArith*>(te->d_theoryTable[THEORY_ARITH]);

    d_realType.reset(new TypeNode(d_nodeManager->realType()));
    d_intType.reset(new TypeNode(d_nodeManager->integerType()));
  }

  void fakeTheoryEnginePreprocess(TNode input)
  {
    Rewriter* rr = d_slvEngine->getEnv().getRewriter();
    Assert(input == rr->rewrite(input));
    TheoryEngine* te = d_slvEngine->d_smtSolver->getTheoryEngine();
    te->preRegister(input);
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
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Node x = d_nodeManager->mkVar(*d_realType);
  Node c = d_nodeManager->mkConstReal(d_zero);

  Node gt = d_nodeManager->mkNode(GT, x, c);
  Node leq = rr->rewrite(gt.notNode());
  fakeTheoryEnginePreprocess(leq);

  d_arith->assertFact(leq, true);

  d_arith->check(d_level);
}

TEST_F(TestTheoryWhiteArith, int_normal_form)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  Node x = d_nodeManager->mkVar(*d_intType);
  Node xr = d_nodeManager->mkVar(*d_realType);
  Node c0 = d_nodeManager->mkConstInt(d_zero);
  Node c1 = d_nodeManager->mkConstInt(d_one);
  Node c2 = d_nodeManager->mkConstInt(Rational(2));

  Node geq0 = d_nodeManager->mkNode(GEQ, x, c0);
  Node geq1 = d_nodeManager->mkNode(GEQ, x, c1);
  Node geq2 = d_nodeManager->mkNode(GEQ, x, c2);

  ASSERT_EQ(rr->rewrite(geq0), geq0);
  ASSERT_EQ(rr->rewrite(geq1), geq1);

  Node gt0 = d_nodeManager->mkNode(GT, x, c0);
  Node gt1 = d_nodeManager->mkNode(GT, x, c1);

  ASSERT_EQ(rr->rewrite(gt0), rr->rewrite(geq1));
  ASSERT_EQ(rr->rewrite(gt1), rr->rewrite(geq2));

  Node lt0 = d_nodeManager->mkNode(LT, x, c0);
  Node lt1 = d_nodeManager->mkNode(LT, x, c1);

  ASSERT_EQ(rr->rewrite(lt0), rr->rewrite(geq0.notNode()));
  ASSERT_EQ(rr->rewrite(lt1), rr->rewrite(geq1.notNode()));

  Node leq0 = d_nodeManager->mkNode(LEQ, x, c0);
  Node leq1 = d_nodeManager->mkNode(LEQ, x, c1);

  ASSERT_EQ(rr->rewrite(leq0), rr->rewrite(geq1.notNode()));
  ASSERT_EQ(rr->rewrite(leq1), rr->rewrite(geq2.notNode()));

  // (abs x) --> (abs x)
  Node absX = d_nodeManager->mkNode(ABS, x);
  ASSERT_EQ(rr->rewrite(absX), absX);

  // (exp (+ 2 + x)) --> (* (exp x) (exp 1) (exp 1))
  Node cr0 = d_nodeManager->mkConstReal(d_zero);
  Node t =
      d_nodeManager->mkNode(EXPONENTIAL, d_nodeManager->mkNode(ADD, c2, xr))
          .eqNode(cr0);
  ASSERT_EQ(rr->rewrite(rr->rewrite(t)), rr->rewrite(t));
}
}  // namespace test
}  // namespace cvc5::internal
