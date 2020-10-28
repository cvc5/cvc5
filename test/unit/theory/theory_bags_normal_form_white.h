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

  void testBagCount()
  {
    // Examples
    // -------
    // (bag.count "x" (emptybag String)) = 0
    // (bag.count "x" (mkBag "y" 5)) = 0
    // (bag.count "x" (mkBag "x" 4)) = 4
    // (bag.count "x" (union_disjoint (mkBag "x" 4) (mkBag "y" 5)) = 4
    // (bag.count "x" (union_disjoint (mkBag "y" 5) (mkBag "z" 5)) = 0

    Node zero = d_nm->mkConst(Rational(0));
    Node four = d_nm->mkConst(Rational(4));
    Node empty = d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));
    Node z = d_nm->mkConst(String("z"));
    Node x_4 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(4)));
    Node y_5 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(5)));
    Node z_5 = d_nm->mkBag(d_nm->stringType(), z, d_nm->mkConst(Rational(5)));

    Node input1 = d_nm->mkNode(BAG_COUNT, x, empty);
    Node output1 = zero;
    TS_ASSERT(output1 == NormalForm::evaluate(input1));

    Node input2 = d_nm->mkNode(BAG_COUNT, x, y_5);
    Node output2 = zero;
    TS_ASSERT(output2 == NormalForm::evaluate(input2));

    Node input3 = d_nm->mkNode(BAG_COUNT, x, x_4);
    Node output3 = four;
    TS_ASSERT(output2 == NormalForm::evaluate(input2));

    Node unionDisjointXY = d_nm->mkNode(UNION_DISJOINT, x_4, y_5);
    Node input4 = d_nm->mkNode(BAG_COUNT, x, unionDisjointXY);
    Node output4 = four;
    TS_ASSERT(output3 == NormalForm::evaluate(input3));

    Node unionDisjointYZ = d_nm->mkNode(UNION_DISJOINT, y_5, z_5);
    Node input5 = d_nm->mkNode(BAG_COUNT, x, unionDisjointYZ);
    Node output5 = zero;
    TS_ASSERT(output4 == NormalForm::evaluate(input4));
  }

  void testDuplicateRemoval()
  {
    // Examples
    // --------
    //  - (duplicate_removal (emptybag String)) = (emptybag String)
    //  - (duplicate_removal (mkBag "x" 4)) = (emptybag "x" 1)
    //  - (duplicate_removal (disjoint_union (mkBag "x" 3) (mkBag "y" 5)) =
    //     (disjoint_union (mkBag "x" 1) (mkBag "y" 1)

    Node emptybag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node input1 = d_nm->mkNode(DUPLICATE_REMOVAL, emptybag);
    Node output1 = emptybag;
    TS_ASSERT(output1 == NormalForm::evaluate(input1));

    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));

    Node x_1 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(1)));
    Node y_1 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(1)));

    Node x_4 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(4)));
    Node y_5 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(5)));

    Node input2 = d_nm->mkNode(DUPLICATE_REMOVAL, x_4);
    Node output2 = x_1;
    TS_ASSERT(output2 == NormalForm::evaluate(input2));

    Node normalBag = d_nm->mkNode(UNION_DISJOINT, x_4, y_5);
    Node input3 = d_nm->mkNode(DUPLICATE_REMOVAL, normalBag);
    Node output3 = d_nm->mkNode(UNION_DISJOINT, x_1, y_1);
    TS_ASSERT(output3 == NormalForm::evaluate(input3));
  }

  void testUnionMax()
  {
    // Example
    // -------
    // input: (union_max A B)
    //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
    //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
    // output:
    //    (union_disjoint A B)
    //        where A = (MK_BAG "x" 4)
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
    Node input = d_nm->mkNode(UNION_MAX, A, B);

    // output
    Node output = d_nm->mkNode(
        UNION_DISJOINT, x_4, d_nm->mkNode(UNION_DISJOINT, y_1, z_2));

    TS_ASSERT(output.isConst());
    TS_ASSERT(output == NormalForm::evaluate(input));
  }

  void testUnionDisjoint1()
  {
    vector<Node> elements = getNStrings(3);
    Node emptybag =
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

  void testIntersectionMin()
  {
    // Example
    // -------
    // input: (intersection_min A B)
    //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
    //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
    // output:
    //    (MK_BAG "x" 3)

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
    Node input = d_nm->mkNode(INTERSECTION_MIN, A, B);

    // output
    Node output = x_3;

    TS_ASSERT(output.isConst());
    TS_ASSERT(output == NormalForm::evaluate(input));
  }

  void testDifferenceSubtract()
  {
    // Example
    // -------
    // input: (difference_subtract A B)
    //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
    //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
    // output:
    //    (union_disjoint (MK_BAG "x" 1) (MK_BAG "z" 2))

    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));
    Node z = d_nm->mkConst(String("z"));
    Node x_1 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(1)));
    Node x_4 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(4)));
    Node x_3 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(3)));
    Node x_7 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(7)));
    Node z_2 = d_nm->mkBag(d_nm->stringType(), z, d_nm->mkConst(Rational(2)));
    Node y_1 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(1)));

    Node A = d_nm->mkNode(UNION_DISJOINT, x_4, z_2);
    Node B = d_nm->mkNode(UNION_DISJOINT, x_3, y_1);
    Node input = d_nm->mkNode(DIFFERENCE_SUBTRACT, A, B);

    // output
    Node output = d_nm->mkNode(UNION_DISJOINT, x_1, z_2);

    TS_ASSERT(output.isConst());
    TS_ASSERT(output == NormalForm::evaluate(input));
  }

  void testDifferenceRemove()
  {
    // Example
    // -------
    // input: (difference_remove A B)
    //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
    //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
    // output:
    //    (MK_BAG "z" 2)

    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));
    Node z = d_nm->mkConst(String("z"));
    Node x_1 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(1)));
    Node x_4 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(4)));
    Node x_3 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(3)));
    Node x_7 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(7)));
    Node z_2 = d_nm->mkBag(d_nm->stringType(), z, d_nm->mkConst(Rational(2)));
    Node y_1 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(1)));

    Node A = d_nm->mkNode(UNION_DISJOINT, x_4, z_2);
    Node B = d_nm->mkNode(UNION_DISJOINT, x_3, y_1);
    Node input = d_nm->mkNode(DIFFERENCE_REMOVE, A, B);

    // output
    Node output = z_2;

    TS_ASSERT(output.isConst());
    TS_ASSERT(output == NormalForm::evaluate(input));
  }

  void testChoose()
  {
    // Example
    // -------
    // input:  (choose (emptybag String))
    // output: "A"; the first element returned by the type enumerator
    // input:  (choose (MK_BAG "x" 4))
    // output: "x"
    // input:  (choose (union_disjoint (MK_BAG "x" 4) (MK_BAG "y" 1)))
    // output: "x"; deterministically return the first element
    Node empty = d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));
    Node z = d_nm->mkConst(String("z"));
    Node x_4 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(4)));
    Node y_1 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(1)));

    Node input1 = d_nm->mkNode(BAG_CHOOSE, empty);
    Node output1 = d_nm->mkConst(String(""));

    TS_ASSERT(output1 == NormalForm::evaluate(input1));

    Node input2 = d_nm->mkNode(BAG_CHOOSE, x_4);
    Node output2 = x;
    TS_ASSERT(output2 == NormalForm::evaluate(input2));

    Node union_disjoint = d_nm->mkNode(UNION_DISJOINT, x_4, y_1);
    Node input3 = d_nm->mkNode(BAG_CHOOSE, union_disjoint);
    Node output3 = x;
    TS_ASSERT(output3 == NormalForm::evaluate(input3));
  }

  void testBagCard()
  {
    // Examples
    // --------
    //  - (card (emptybag String)) = 0
    //  - (choose (MK_BAG "x" 4)) = 4
    //  - (choose (union_disjoint (MK_BAG "x" 4) (MK_BAG "y" 1))) = 5
    Node empty = d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));
    Node z = d_nm->mkConst(String("z"));
    Node x_4 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(4)));
    Node y_1 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(1)));

    Node input1 = d_nm->mkNode(BAG_CARD, empty);
    Node output1 = d_nm->mkConst(Rational(0));

    TS_ASSERT(output1 == NormalForm::evaluate(input1));

    Node input2 = d_nm->mkNode(BAG_CARD, x_4);
    Node output2 = d_nm->mkConst(Rational(4));
    TS_ASSERT(output2 == NormalForm::evaluate(input2));

    Node union_disjoint = d_nm->mkNode(UNION_DISJOINT, x_4, y_1);
    Node input3 = d_nm->mkNode(BAG_CARD, union_disjoint);
    Node output3 = d_nm->mkConst(Rational(5));
    TS_ASSERT(output3 == NormalForm::evaluate(input3));
  }

  void testIsSingleton()
  {
    // Examples
    // --------
    //  - (bag.is_singleton (emptybag String)) = false
    //  - (bag.is_singleton (MK_BAG "x" 1)) = true
    //  - (bag.is_singleton (MK_BAG "x" 4)) = false
    //  - (bag.is_singleton (union_disjoint (MK_BAG "x" 1) (MK_BAG "y" 1))) =
    //     false
    Node falseNode = d_nm->mkConst(false);
    Node trueNode = d_nm->mkConst(true);
    Node empty = d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));
    Node z = d_nm->mkConst(String("z"));
    Node x_1 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(1)));
    Node x_4 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(4)));
    Node y_1 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(1)));

    Node input1 = d_nm->mkNode(BAG_IS_SINGLETON, empty);
    Node output1 = falseNode;
    TS_ASSERT(output1 == NormalForm::evaluate(input1));

    Node input2 = d_nm->mkNode(BAG_IS_SINGLETON, x_1);
    Node output2 = trueNode;
    TS_ASSERT(output2 == NormalForm::evaluate(input2));

    Node input3 = d_nm->mkNode(BAG_IS_SINGLETON, x_4);
    Node output3 = falseNode;
    TS_ASSERT(output2 == NormalForm::evaluate(input2));

    Node union_disjoint = d_nm->mkNode(UNION_DISJOINT, x_1, y_1);
    Node input4 = d_nm->mkNode(BAG_IS_SINGLETON, union_disjoint);
    Node output4 = falseNode;
    TS_ASSERT(output3 == NormalForm::evaluate(input3));
  }

  void testFromSet()
  {
    // Examples
    // --------
    //  - (bag.from_set (emptyset String)) = (emptybag String)
    //  - (bag.from_set (singleton "x")) = (mkBag "x" 1)
    //  - (bag.to_set (union (singleton "x") (singleton "y"))) =
    //     (disjoint_union (mkBag "x" 1) (mkBag "y" 1))

    Node emptyset =
        d_nm->mkConst(EmptySet(d_nm->mkSetType(d_nm->stringType())));
    Node emptybag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node input1 = d_nm->mkNode(BAG_FROM_SET, emptyset);
    Node output1 = emptybag;
    TS_ASSERT(output1 == NormalForm::evaluate(input1));

    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));

    Node xSingleton = d_nm->mkSingleton(d_nm->stringType(), x);
    Node ySingleton = d_nm->mkSingleton(d_nm->stringType(), y);

    Node x_1 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(1)));
    Node y_1 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(1)));

    Node input2 = d_nm->mkNode(BAG_FROM_SET, xSingleton);
    Node output2 = x_1;
    TS_ASSERT(output2 == NormalForm::evaluate(input2));

    // for normal sets, the first node is the largest, not smallest
    Node normalSet = d_nm->mkNode(UNION, ySingleton, xSingleton);
    Node input3 = d_nm->mkNode(BAG_FROM_SET, normalSet);
    Node output3 = d_nm->mkNode(UNION_DISJOINT, x_1, y_1);
    TS_ASSERT(output3 == NormalForm::evaluate(input3));
  }

  void testToSet()
  {
    // Examples
    // --------
    //  - (bag.to_set (emptybag String)) = (emptyset String)
    //  - (bag.to_set (mkBag "x" 4)) = (singleton "x")
    //  - (bag.to_set (disjoint_union (mkBag "x" 3) (mkBag "y" 5)) =
    //     (union (singleton "x") (singleton "y")))

    Node emptyset =
        d_nm->mkConst(EmptySet(d_nm->mkSetType(d_nm->stringType())));
    Node emptybag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node input1 = d_nm->mkNode(BAG_TO_SET, emptybag);
    Node output1 = emptyset;
    TS_ASSERT(output1 == NormalForm::evaluate(input1));

    Node x = d_nm->mkConst(String("x"));
    Node y = d_nm->mkConst(String("y"));

    Node xSingleton = d_nm->mkSingleton(d_nm->stringType(), x);
    Node ySingleton = d_nm->mkSingleton(d_nm->stringType(), y);

    Node x_4 = d_nm->mkBag(d_nm->stringType(), x, d_nm->mkConst(Rational(4)));
    Node y_5 = d_nm->mkBag(d_nm->stringType(), y, d_nm->mkConst(Rational(5)));

    Node input2 = d_nm->mkNode(BAG_TO_SET, x_4);
    Node output2 = xSingleton;
    TS_ASSERT(output2 == NormalForm::evaluate(input2));

    // for normal sets, the first node is the largest, not smallest
    Node normalBag = d_nm->mkNode(UNION_DISJOINT, x_4, y_5);
    Node input3 = d_nm->mkNode(BAG_TO_SET, normalBag);
    Node output3 = d_nm->mkNode(UNION, ySingleton, xSingleton);
    TS_ASSERT(output3 == NormalForm::evaluate(input3));
  }

 private:
  std::unique_ptr<ExprManager> d_em;
  std::unique_ptr<SmtEngine> d_smt;
  std::unique_ptr<NodeManager> d_nm;
  std::unique_ptr<BagsRewriter> d_rewriter;
}; /* class BagsTypeRuleBlack */
