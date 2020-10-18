/*********************                                                        */
/*! \file theory_bags_normal_form_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of bags normal form
 **/

#include <cxxtest/TestSuite.h>

#include "expr/dtype.h"
#include "smt/smt_engine.h"
#include "theory/bags/bags_rewriter.h"
#include "theory/bags/normal_form.h"
#include "theory/strings/type_enumerator.h"

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::kind;
using namespace CVC4::theory::bags;
using namespace std;

typedef expr::Attribute<Node, Node> attribute;

class BagsNormalFormWhite : public CxxTest::TestSuite
{
 public:
  void setUp() override
  {
    d_em.reset(new ExprManager());
    d_smt.reset(new SmtEngine(d_em.get()));
    d_nm.reset(NodeManager::fromExprManager(d_em.get()));
    d_smt->finishInit();
    d_rewriter.reset(new BagsRewriter(nullptr));
  }

  void tearDown() override
  {
    d_rewriter.reset();
    d_smt.reset();
    d_nm.release();
    d_em.reset();
  }

  std::vector<Node> getNStrings(size_t n)
  {
    std::vector<Node> elements(n);
    CVC4::theory::strings::StringEnumerator enumerator(d_nm->stringType());

    for (size_t i = 0; i < n; i++)
    {
      ++enumerator;
      elements[i] = *enumerator;
    }

    return elements;
  }

  void testEmptyBagNormalForm()
  {
    Node emptybag = d_nm->mkConst(EmptyBag(d_nm->stringType()));
    // empty bags are in normal form
    TS_ASSERT(emptybag.isConst());
    Node n = NormalForm::evaluate(emptybag);
    TS_ASSERT(emptybag == n);
  }

  void testBagEquality() {}

  void testMkBagConstantElement()
  {
    vector<Node> elements = getNStrings(1);
    Node negative = d_nm->mkBag(
        d_nm->stringType(), elements[0], d_nm->mkConst(Rational(-1)));
    Node zero = d_nm->mkBag(
        d_nm->stringType(), elements[0], d_nm->mkConst(Rational(0)));
    Node positive = d_nm->mkBag(
        d_nm->stringType(), elements[0], d_nm->mkConst(Rational(1)));
    Node emptybag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));

    TS_ASSERT(!negative.isConst());
    TS_ASSERT(!zero.isConst());
    TS_ASSERT(emptybag == NormalForm::evaluate(negative));
    TS_ASSERT(emptybag == NormalForm::evaluate(zero));
    TS_ASSERT(positive == NormalForm::evaluate(positive));
  }

  void testBagCount() {}

  void testUnionMax() {}

  void testUnionDisjoint1()
  {
    vector<Node> elements = getNStrings(3);
    Node emptyBag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node A = d_nm->mkBag(
        d_nm->stringType(), elements[0], d_nm->mkConst(Rational(2)));
    Node B = d_nm->mkBag(
        d_nm->stringType(), elements[1], d_nm->mkConst(Rational(3)));
    Node C = d_nm->mkBag(
        d_nm->stringType(), elements[2], d_nm->mkConst(Rational(4)));

    Node unionDisjointAB = d_nm->mkNode(UNION_DISJOINT, A, B);
    // unionDisjointAB is already in a normal form
    TS_ASSERT(unionDisjointAB.isConst());
    TS_ASSERT(unionDisjointAB == NormalForm::evaluate(unionDisjointAB));

    Node unionDisjointBA = d_nm->mkNode(UNION_DISJOINT, B, A);
    // unionDisjointAB is is the normal form of unionDisjointBA
    TS_ASSERT(!unionDisjointBA.isConst());
    TS_ASSERT(unionDisjointAB == NormalForm::evaluate(unionDisjointBA));

    Node unionDisjointAB_C = d_nm->mkNode(UNION_DISJOINT, unionDisjointAB, C);
    Node unionDisjointBC = d_nm->mkNode(UNION_DISJOINT, B, C);
    Node unionDisjointA_BC = d_nm->mkNode(UNION_DISJOINT, A, unionDisjointBC);
    // unionDisjointA_BC is the normal form of unionDisjointAB_C
    TS_ASSERT(!unionDisjointAB_C.isConst());
    TS_ASSERT(unionDisjointA_BC.isConst());
    TS_ASSERT(unionDisjointA_BC == NormalForm::evaluate(unionDisjointAB_C));

    Node unionDisjointAA = d_nm->mkNode(UNION_DISJOINT, A, A);
    Node AA = d_nm->mkBag(
        d_nm->stringType(), elements[0], d_nm->mkConst(Rational(4)));
    TS_ASSERT(!unionDisjointAA.isConst());
    TS_ASSERT(AA.isConst());
    TS_ASSERT(AA == NormalForm::evaluate(unionDisjointAA));
  }

  void testUnionDisjoint2()
  {
    // Example
    // -------
    // input: (union_disjoint A B)
    //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
    //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
    // output:
    //    (union_disjoint A B)
    //        where A = (MK_BAG "x" 7)
    //              B = (union_disjoint (MK_BAG "y" 1) (MK_BAG "z" 2)))

    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));
    Node z = d_nm->mkConst(String("z"));
    Node x_4 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(4)));
    Node x_3 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(3)));
    Node x_7 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(7)));
    Node z_2 = d_nm->mkBag(d_nm->stringType(), z, d_nm->mkConst(Rational(2)));
    Node y_1 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(1)));

    Node A = d_nm->mkNode(UNION_DISJOINT, x_4, z_2);
    Node B = d_nm->mkNode(UNION_DISJOINT, x_3, y_1);
    Node input = d_nm->mkNode(UNION_DISJOINT, A, B);

    // output
    Node output = d_nm->mkNode(
        UNION_DISJOINT, x_7, d_nm->mkNode(UNION_DISJOINT, y_1, z_2));

    TS_ASSERT(output.isConst());
    TS_ASSERT(output == NormalForm::evaluate(input));
  }

  void testIntersectionMin() {}

  void testDifferenceSubtract() {}

  void testDifferenceRemove() {}

  void testChoose() {}

  void testBagCard() {}

  void testIsSingleton() {}

 private:
  std::unique_ptr<ExprManager> d_em;
  std::unique_ptr<SmtEngine> d_smt;
  std::unique_ptr<NodeManager> d_nm;

  std::unique_ptr<BagsRewriter> d_rewriter;
}; /* class BagsTypeRuleBlack */
