/*********************                                                        */
/*! \file theory_arith_white.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Whitebox tests for theory Arithmetic.
 **/

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

namespace CVC4 {

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
    d_context = d_smtEngine->getContext();
    d_user_context = d_smtEngine->getUserContext();
    d_outputChannel.clear();
    d_logicInfo.lock();
    d_smtEngine->getTheoryEngine()
        ->d_theoryTable[THEORY_ARITH]
        ->setOutputChannel(d_outputChannel);
    d_arith = static_cast<TheoryArith*>(
        d_smtEngine->getTheoryEngine()->d_theoryTable[THEORY_ARITH]);

    d_preregistered.reset(new std::set<Node>());

    d_booleanType.reset(new TypeNode(d_nodeManager->booleanType()));
    d_realType.reset(new TypeNode(d_nodeManager->realType()));
    d_intType.reset(new TypeNode(d_nodeManager->integerType()));
  }

  void fakeTheoryEnginePreprocess(TNode input)
  {
    Assert(input == Rewriter::rewrite(input));
    Node rewrite = input;
    if (d_debug)
    {
      std::cout << "input " << input << " rewrite " << rewrite << std::endl;
    }

    std::list<Node> toPreregister;

    toPreregister.push_back(rewrite);
    for (std::list<Node>::iterator i = toPreregister.begin();
         i != toPreregister.end();
         ++i)
    {
      Node n = *i;
      d_preregistered->insert(n);

      for (Node::iterator citer = n.begin(); citer != n.end(); ++citer)
      {
        Node c = *citer;
        if (d_preregistered->find(c) == d_preregistered->end())
        {
          toPreregister.push_back(c);
        }
      }
    }
    for (std::list<Node>::reverse_iterator i = toPreregister.rbegin();
         i != toPreregister.rend();
         ++i)
    {
      Node n = *i;
      if (d_debug)
      {
        std::cout << "id " << n.getId() << " " << n << std::endl;
      }
      d_arith->preRegisterTerm(n);
    }
  }

  Context* d_context;
  UserContext* d_user_context;
  DummyOutputChannel d_outputChannel;
  LogicInfo d_logicInfo;
  Theory::Effort d_level = Theory::EFFORT_FULL;
  TheoryArith* d_arith;
  std::unique_ptr<std::set<Node>> d_preregistered;
  std::unique_ptr<TypeNode> d_booleanType;
  std::unique_ptr<TypeNode> d_realType;
  std::unique_ptr<TypeNode> d_intType;
  const Rational d_zero = 0;
  const Rational d_one = 1;
  bool d_debug = false;
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

  ASSERT_EQ(d_outputChannel.getNumCalls(), 0u);
}

TEST_F(TestTheoryWhiteArith, TPLt1)
{
  Node x = d_nodeManager->mkVar(*d_realType);
  Node c0 = d_nodeManager->mkConst<Rational>(d_zero);
  Node c1 = d_nodeManager->mkConst<Rational>(d_one);

  Node gt0 = d_nodeManager->mkNode(GT, x, c0);
  Node gt1 = d_nodeManager->mkNode(GT, x, c1);
  Node geq1 = d_nodeManager->mkNode(GEQ, x, c1);
  Node leq0 = Rewriter::rewrite(gt0.notNode());
  Node leq1 = Rewriter::rewrite(gt1.notNode());
  Node lt1 = Rewriter::rewrite(geq1.notNode());

  fakeTheoryEnginePreprocess(leq0);
  fakeTheoryEnginePreprocess(leq1);
  fakeTheoryEnginePreprocess(geq1);

  d_arith->presolve();
  d_arith->assertFact(lt1, true);
  d_arith->check(d_level);
  d_arith->propagate(d_level);

  Node gt0OrLt1 = NodeBuilder<2>(OR) << gt0 << lt1;
  Node geq0OrLeq1 = NodeBuilder<2>(OR) << geq1 << leq1;
  gt0OrLt1 = Rewriter::rewrite(gt0OrLt1);
  geq0OrLeq1 = Rewriter::rewrite(geq0OrLeq1);

  std::cout << d_outputChannel.getIthNode(0) << std::endl << std::endl;
  std::cout << d_outputChannel.getIthNode(1) << std::endl << std::endl;
  std::cout << d_outputChannel.getIthNode(2) << std::endl << std::endl;

  ASSERT_EQ(d_outputChannel.getNumCalls(), 3u);

  ASSERT_EQ(d_outputChannel.getIthCallType(0), LEMMA);
  ASSERT_TRUE(d_outputChannel.getIthNode(0) == gt0OrLt1);

  ASSERT_EQ(d_outputChannel.getIthCallType(1), LEMMA);
  ASSERT_TRUE(d_outputChannel.getIthNode(1) == geq0OrLeq1);

  ASSERT_EQ(d_outputChannel.getIthCallType(2), PROPAGATE);
  ASSERT_EQ(d_outputChannel.getIthNode(2), leq1);
}

TEST_F(TestTheoryWhiteArith, TPLeq0)
{
  Node x = d_nodeManager->mkVar(*d_realType);
  Node c0 = d_nodeManager->mkConst<Rational>(d_zero);
  Node c1 = d_nodeManager->mkConst<Rational>(d_one);

  Node gt0 = d_nodeManager->mkNode(GT, x, c0);
  Node gt1 = d_nodeManager->mkNode(GT, x, c1);
  Node geq1 = d_nodeManager->mkNode(GEQ, x, c1);
  Node leq0 = Rewriter::rewrite(gt0.notNode());
  Node leq1 = Rewriter::rewrite(gt1.notNode());
  Node lt1 = Rewriter::rewrite(geq1.notNode());

  fakeTheoryEnginePreprocess(leq0);
  fakeTheoryEnginePreprocess(leq1);
  fakeTheoryEnginePreprocess(geq1);

  d_arith->presolve();
  d_arith->assertFact(leq0, true);
  d_arith->check(d_level);
  d_arith->propagate(d_level);

  Node gt0OrLt1 = NodeBuilder<2>(OR) << gt0 << lt1;
  Node geq0OrLeq1 = NodeBuilder<2>(OR) << geq1 << leq1;
  gt0OrLt1 = Rewriter::rewrite(gt0OrLt1);
  geq0OrLeq1 = Rewriter::rewrite(geq0OrLeq1);

  std::cout << d_outputChannel.getIthNode(0) << std::endl;
  std::cout << d_outputChannel.getIthNode(1) << std::endl;
  std::cout << d_outputChannel.getIthNode(2) << std::endl;
  std::cout << d_outputChannel.getIthNode(3) << std::endl;

  ASSERT_EQ(d_outputChannel.getNumCalls(), 4u);

  ASSERT_EQ(d_outputChannel.getIthCallType(0), LEMMA);
  ASSERT_EQ(d_outputChannel.getIthNode(0), gt0OrLt1);

  ASSERT_EQ(d_outputChannel.getIthCallType(1), LEMMA);
  ASSERT_EQ(d_outputChannel.getIthNode(1), geq0OrLeq1);

  ASSERT_EQ(d_outputChannel.getIthCallType(2), PROPAGATE);
  ASSERT_EQ(d_outputChannel.getIthNode(2), lt1);

  ASSERT_EQ(d_outputChannel.getIthCallType(3), PROPAGATE);
  ASSERT_EQ(d_outputChannel.getIthNode(3), leq1);
}

TEST_F(TestTheoryWhiteArith, TPLeq1)
{
  Node x = d_nodeManager->mkVar(*d_realType);
  Node c0 = d_nodeManager->mkConst<Rational>(d_zero);
  Node c1 = d_nodeManager->mkConst<Rational>(d_one);

  Node gt0 = d_nodeManager->mkNode(GT, x, c0);
  Node gt1 = d_nodeManager->mkNode(GT, x, c1);
  Node geq1 = d_nodeManager->mkNode(GEQ, x, c1);
  Node leq0 = Rewriter::rewrite(gt0.notNode());
  Node leq1 = Rewriter::rewrite(gt1.notNode());
  Node lt1 = Rewriter::rewrite(geq1.notNode());

  fakeTheoryEnginePreprocess(leq0);
  fakeTheoryEnginePreprocess(leq1);
  fakeTheoryEnginePreprocess(geq1);

  d_arith->presolve();
  d_arith->assertFact(leq1, true);
  d_arith->check(d_level);
  d_arith->propagate(d_level);

  Node gt0OrLt1 = NodeBuilder<2>(OR) << gt0 << lt1;
  Node geq0OrLeq1 = NodeBuilder<2>(OR) << geq1 << leq1;
  gt0OrLt1 = Rewriter::rewrite(gt0OrLt1);
  geq0OrLeq1 = Rewriter::rewrite(geq0OrLeq1);

  std::cout << d_outputChannel.getIthNode(0) << std::endl;
  std::cout << d_outputChannel.getIthNode(1) << std::endl;

  ASSERT_EQ(d_outputChannel.getNumCalls(), 2u);

  ASSERT_EQ(d_outputChannel.getIthCallType(0), LEMMA);
  ASSERT_EQ(d_outputChannel.getIthNode(0), gt0OrLt1);

  ASSERT_EQ(d_outputChannel.getIthCallType(1), LEMMA);
  ASSERT_EQ(d_outputChannel.getIthNode(1), geq0OrLeq1);
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
}  // namespace CVC4
