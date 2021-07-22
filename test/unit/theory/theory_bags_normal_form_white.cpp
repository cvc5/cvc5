/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of bags normal form
 */

#include "expr/dtype.h"
#include "expr/emptybag.h"
#include "expr/emptyset.h"
#include "test_smt.h"
#include "theory/bags/bags_rewriter.h"
#include "theory/bags/normal_form.h"
#include "theory/strings/type_enumerator.h"
#include "util/rational.h"
#include "util/string.h"

namespace cvc5 {

using namespace theory;
using namespace kind;
using namespace theory::bags;

namespace test {

typedef expr::Attribute<Node, Node> attribute;

class TestTheoryWhiteBagsNormalForm : public TestSmt
{
 protected:
  void SetUp() override
  {
    TestSmt::SetUp();
    d_rewriter.reset(new BagsRewriter(nullptr));
  }

  std::vector<Node> getNStrings(size_t n)
  {
    std::vector<Node> elements(n);
    cvc5::theory::strings::StringEnumerator enumerator(
        d_nodeManager->stringType());

    for (size_t i = 0; i < n; i++)
    {
      ++enumerator;
      elements[i] = *enumerator;
    }

    return elements;
  }

  std::unique_ptr<BagsRewriter> d_rewriter;
};

TEST_F(TestTheoryWhiteBagsNormalForm, empty_bag_normal_form)
{
  Node emptybag = d_nodeManager->mkConst(EmptyBag(d_nodeManager->stringType()));
  // empty bags are in normal form
  ASSERT_TRUE(emptybag.isConst());
  Node n = NormalForm::evaluate(emptybag);
  ASSERT_EQ(emptybag, n);
}

TEST_F(TestTheoryWhiteBagsNormalForm, mkBag_constant_element)
{
  std::vector<Node> elements = getNStrings(1);
  Node negative = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                       elements[0],
                                       d_nodeManager->mkConst(Rational(-1)));
  Node zero = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                   elements[0],
                                   d_nodeManager->mkConst(Rational(0)));
  Node positive = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                       elements[0],
                                       d_nodeManager->mkConst(Rational(1)));
  Node emptybag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));

  ASSERT_FALSE(negative.isConst());
  ASSERT_FALSE(zero.isConst());
  ASSERT_EQ(emptybag, NormalForm::evaluate(negative));
  ASSERT_EQ(emptybag, NormalForm::evaluate(zero));
  ASSERT_EQ(positive, NormalForm::evaluate(positive));
}

TEST_F(TestTheoryWhiteBagsNormalForm, bag_count)
{
  // Examples
  // -------
  // (bag.count "x" (emptybag String)) = 0
  // (bag.count "x" (mkBag "y" 5)) = 0
  // (bag.count "x" (mkBag "x" 4)) = 4
  // (bag.count "x" (union_disjoint (mkBag "x" 4) (mkBag "y" 5)) = 4
  // (bag.count "x" (union_disjoint (mkBag "y" 5) (mkBag "z" 5)) = 0

  Node zero = d_nodeManager->mkConst(Rational(0));
  Node four = d_nodeManager->mkConst(Rational(4));
  Node empty = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));
  Node z = d_nodeManager->mkConst(String("z"));
  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node y_5 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(5)));
  Node z_5 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), z, d_nodeManager->mkConst(Rational(5)));

  Node input1 = d_nodeManager->mkNode(BAG_COUNT, x, empty);
  Node output1 = zero;
  ASSERT_EQ(output1, NormalForm::evaluate(input1));

  Node input2 = d_nodeManager->mkNode(BAG_COUNT, x, y_5);
  Node output2 = zero;
  ASSERT_EQ(output2, NormalForm::evaluate(input2));

  Node input3 = d_nodeManager->mkNode(BAG_COUNT, x, x_4);
  Node output3 = four;
  ASSERT_EQ(output2, NormalForm::evaluate(input2));

  Node unionDisjointXY = d_nodeManager->mkNode(UNION_DISJOINT, x_4, y_5);
  Node input4 = d_nodeManager->mkNode(BAG_COUNT, x, unionDisjointXY);
  Node output4 = four;
  ASSERT_EQ(output3, NormalForm::evaluate(input3));

  Node unionDisjointYZ = d_nodeManager->mkNode(UNION_DISJOINT, y_5, z_5);
  Node input5 = d_nodeManager->mkNode(BAG_COUNT, x, unionDisjointYZ);
  Node output5 = zero;
  ASSERT_EQ(output4, NormalForm::evaluate(input4));
}

TEST_F(TestTheoryWhiteBagsNormalForm, duplicate_removal)
{
  // Examples
  // --------
  //  - (duplicate_removal (emptybag String)) = (emptybag String)
  //  - (duplicate_removal (mkBag "x" 4)) = (emptybag "x" 1)
  //  - (duplicate_removal (disjoint_union (mkBag "x" 3) (mkBag "y" 5)) =
  //     (disjoint_union (mkBag "x" 1) (mkBag "y" 1)

  Node emptybag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node input1 = d_nodeManager->mkNode(DUPLICATE_REMOVAL, emptybag);
  Node output1 = emptybag;
  ASSERT_EQ(output1, NormalForm::evaluate(input1));

  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));

  Node x_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(1)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node y_5 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(5)));

  Node input2 = d_nodeManager->mkNode(DUPLICATE_REMOVAL, x_4);
  Node output2 = x_1;
  ASSERT_EQ(output2, NormalForm::evaluate(input2));

  Node normalBag = d_nodeManager->mkNode(UNION_DISJOINT, x_4, y_5);
  Node input3 = d_nodeManager->mkNode(DUPLICATE_REMOVAL, normalBag);
  Node output3 = d_nodeManager->mkNode(UNION_DISJOINT, x_1, y_1);
  ASSERT_EQ(output3, NormalForm::evaluate(input3));
}

TEST_F(TestTheoryWhiteBagsNormalForm, union_max)
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

  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));
  Node z = d_nodeManager->mkConst(String("z"));
  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node x_3 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(3)));
  Node x_7 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(7)));
  Node z_2 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), z, d_nodeManager->mkConst(Rational(2)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node A = d_nodeManager->mkNode(UNION_DISJOINT, x_4, z_2);
  Node B = d_nodeManager->mkNode(UNION_DISJOINT, x_3, y_1);
  Node input = d_nodeManager->mkNode(UNION_MAX, A, B);

  // output
  Node output = d_nodeManager->mkNode(
      UNION_DISJOINT, x_4, d_nodeManager->mkNode(UNION_DISJOINT, y_1, z_2));

  ASSERT_TRUE(output.isConst());
  ASSERT_EQ(output, NormalForm::evaluate(input));
}

TEST_F(TestTheoryWhiteBagsNormalForm, union_disjoint1)
{
  std::vector<Node> elements = getNStrings(3);
  Node emptybag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node A = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[0],
                                d_nodeManager->mkConst(Rational(2)));
  Node B = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[1],
                                d_nodeManager->mkConst(Rational(3)));
  Node C = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[2],
                                d_nodeManager->mkConst(Rational(4)));

  Node unionDisjointAB = d_nodeManager->mkNode(UNION_DISJOINT, A, B);
  // unionDisjointAB is already in a normal form
  ASSERT_TRUE(unionDisjointAB.isConst());
  ASSERT_EQ(unionDisjointAB, NormalForm::evaluate(unionDisjointAB));

  Node unionDisjointBA = d_nodeManager->mkNode(UNION_DISJOINT, B, A);
  // unionDisjointAB is is the normal form of unionDisjointBA
  ASSERT_FALSE(unionDisjointBA.isConst());
  ASSERT_EQ(unionDisjointAB, NormalForm::evaluate(unionDisjointBA));

  Node unionDisjointAB_C =
      d_nodeManager->mkNode(UNION_DISJOINT, unionDisjointAB, C);
  Node unionDisjointBC = d_nodeManager->mkNode(UNION_DISJOINT, B, C);
  Node unionDisjointA_BC =
      d_nodeManager->mkNode(UNION_DISJOINT, A, unionDisjointBC);
  // unionDisjointA_BC is the normal form of unionDisjointAB_C
  ASSERT_FALSE(unionDisjointAB_C.isConst());
  ASSERT_TRUE(unionDisjointA_BC.isConst());
  ASSERT_EQ(unionDisjointA_BC, NormalForm::evaluate(unionDisjointAB_C));

  Node unionDisjointAA = d_nodeManager->mkNode(UNION_DISJOINT, A, A);
  Node AA = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                 elements[0],
                                 d_nodeManager->mkConst(Rational(4)));
  ASSERT_FALSE(unionDisjointAA.isConst());
  ASSERT_TRUE(AA.isConst());
  ASSERT_EQ(AA, NormalForm::evaluate(unionDisjointAA));
}

TEST_F(TestTheoryWhiteBagsNormalForm, union_disjoint2)
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

  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));
  Node z = d_nodeManager->mkConst(String("z"));
  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node x_3 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(3)));
  Node x_7 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(7)));
  Node z_2 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), z, d_nodeManager->mkConst(Rational(2)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node A = d_nodeManager->mkNode(UNION_DISJOINT, x_4, z_2);
  Node B = d_nodeManager->mkNode(UNION_DISJOINT, x_3, y_1);
  Node input = d_nodeManager->mkNode(UNION_DISJOINT, A, B);

  // output
  Node output = d_nodeManager->mkNode(
      UNION_DISJOINT, x_7, d_nodeManager->mkNode(UNION_DISJOINT, y_1, z_2));

  ASSERT_TRUE(output.isConst());
  ASSERT_EQ(output, NormalForm::evaluate(input));
}

TEST_F(TestTheoryWhiteBagsNormalForm, intersection_min)
{
  // Example
  // -------
  // input: (intersection_min A B)
  //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
  //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
  // output:
  //    (MK_BAG "x" 3)

  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));
  Node z = d_nodeManager->mkConst(String("z"));
  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node x_3 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(3)));
  Node x_7 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(7)));
  Node z_2 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), z, d_nodeManager->mkConst(Rational(2)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node A = d_nodeManager->mkNode(UNION_DISJOINT, x_4, z_2);
  Node B = d_nodeManager->mkNode(UNION_DISJOINT, x_3, y_1);
  Node input = d_nodeManager->mkNode(INTERSECTION_MIN, A, B);

  // output
  Node output = x_3;

  ASSERT_TRUE(output.isConst());
  ASSERT_EQ(output, NormalForm::evaluate(input));
}

TEST_F(TestTheoryWhiteBagsNormalForm, difference_subtract)
{
  // Example
  // -------
  // input: (difference_subtract A B)
  //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
  //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
  // output:
  //    (union_disjoint (MK_BAG "x" 1) (MK_BAG "z" 2))

  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));
  Node z = d_nodeManager->mkConst(String("z"));
  Node x_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(1)));
  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node x_3 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(3)));
  Node x_7 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(7)));
  Node z_2 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), z, d_nodeManager->mkConst(Rational(2)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node A = d_nodeManager->mkNode(UNION_DISJOINT, x_4, z_2);
  Node B = d_nodeManager->mkNode(UNION_DISJOINT, x_3, y_1);
  Node input = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, A, B);

  // output
  Node output = d_nodeManager->mkNode(UNION_DISJOINT, x_1, z_2);

  ASSERT_TRUE(output.isConst());
  ASSERT_EQ(output, NormalForm::evaluate(input));
}

TEST_F(TestTheoryWhiteBagsNormalForm, difference_remove)
{
  // Example
  // -------
  // input: (difference_remove A B)
  //    where A = (union_disjoint (MK_BAG "x" 4) (MK_BAG "z" 2)))
  //          B = (union_disjoint (MK_BAG "x" 3) (MK_BAG "y" 1)))
  // output:
  //    (MK_BAG "z" 2)

  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));
  Node z = d_nodeManager->mkConst(String("z"));
  Node x_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(1)));
  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node x_3 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(3)));
  Node x_7 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(7)));
  Node z_2 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), z, d_nodeManager->mkConst(Rational(2)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node A = d_nodeManager->mkNode(UNION_DISJOINT, x_4, z_2);
  Node B = d_nodeManager->mkNode(UNION_DISJOINT, x_3, y_1);
  Node input = d_nodeManager->mkNode(DIFFERENCE_REMOVE, A, B);

  // output
  Node output = z_2;

  ASSERT_TRUE(output.isConst());
  ASSERT_EQ(output, NormalForm::evaluate(input));
}

TEST_F(TestTheoryWhiteBagsNormalForm, choose)
{
  // Example
  // -------
  // input:  (choose (emptybag String))
  // output: "A"; the first element returned by the type enumerator
  // input:  (choose (MK_BAG "x" 4))
  // output: "x"
  // input:  (choose (union_disjoint (MK_BAG "x" 4) (MK_BAG "y" 1)))
  // output: "x"; deterministically return the first element
  Node empty = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));
  Node z = d_nodeManager->mkConst(String("z"));
  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node input1 = d_nodeManager->mkNode(BAG_CHOOSE, empty);
  Node output1 = d_nodeManager->mkConst(String(""));

  ASSERT_EQ(output1, NormalForm::evaluate(input1));

  Node input2 = d_nodeManager->mkNode(BAG_CHOOSE, x_4);
  Node output2 = x;
  ASSERT_EQ(output2, NormalForm::evaluate(input2));

  Node union_disjoint = d_nodeManager->mkNode(UNION_DISJOINT, x_4, y_1);
  Node input3 = d_nodeManager->mkNode(BAG_CHOOSE, union_disjoint);
  Node output3 = x;
  ASSERT_EQ(output3, NormalForm::evaluate(input3));
}

TEST_F(TestTheoryWhiteBagsNormalForm, bag_card)
{
  // Examples
  // --------
  //  - (card (emptybag String)) = 0
  //  - (choose (MK_BAG "x" 4)) = 4
  //  - (choose (union_disjoint (MK_BAG "x" 4) (MK_BAG "y" 1))) = 5
  Node empty = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));
  Node z = d_nodeManager->mkConst(String("z"));
  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node input1 = d_nodeManager->mkNode(BAG_CARD, empty);
  Node output1 = d_nodeManager->mkConst(Rational(0));

  ASSERT_EQ(output1, NormalForm::evaluate(input1));

  Node input2 = d_nodeManager->mkNode(BAG_CARD, x_4);
  Node output2 = d_nodeManager->mkConst(Rational(4));
  ASSERT_EQ(output2, NormalForm::evaluate(input2));

  Node union_disjoint = d_nodeManager->mkNode(UNION_DISJOINT, x_4, y_1);
  Node input3 = d_nodeManager->mkNode(BAG_CARD, union_disjoint);
  Node output3 = d_nodeManager->mkConst(Rational(5));
  ASSERT_EQ(output3, NormalForm::evaluate(input3));
}

TEST_F(TestTheoryWhiteBagsNormalForm, is_singleton)
{
  // Examples
  // --------
  //  - (bag.is_singleton (emptybag String)) = false
  //  - (bag.is_singleton (MK_BAG "x" 1)) = true
  //  - (bag.is_singleton (MK_BAG "x" 4)) = false
  //  - (bag.is_singleton (union_disjoint (MK_BAG "x" 1) (MK_BAG "y" 1))) =
  //     false
  Node falseNode = d_nodeManager->mkConst(false);
  Node trueNode = d_nodeManager->mkConst(true);
  Node empty = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));
  Node z = d_nodeManager->mkConst(String("z"));
  Node x_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(1)));
  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node input1 = d_nodeManager->mkNode(BAG_IS_SINGLETON, empty);
  Node output1 = falseNode;
  ASSERT_EQ(output1, NormalForm::evaluate(input1));

  Node input2 = d_nodeManager->mkNode(BAG_IS_SINGLETON, x_1);
  Node output2 = trueNode;
  ASSERT_EQ(output2, NormalForm::evaluate(input2));

  Node input3 = d_nodeManager->mkNode(BAG_IS_SINGLETON, x_4);
  Node output3 = falseNode;
  ASSERT_EQ(output2, NormalForm::evaluate(input2));

  Node union_disjoint = d_nodeManager->mkNode(UNION_DISJOINT, x_1, y_1);
  Node input4 = d_nodeManager->mkNode(BAG_IS_SINGLETON, union_disjoint);
  Node output4 = falseNode;
  ASSERT_EQ(output3, NormalForm::evaluate(input3));
}

TEST_F(TestTheoryWhiteBagsNormalForm, from_set)
{
  // Examples
  // --------
  //  - (bag.from_set (emptyset String)) = (emptybag String)
  //  - (bag.from_set (singleton "x")) = (mkBag "x" 1)
  //  - (bag.to_set (union (singleton "x") (singleton "y"))) =
  //     (disjoint_union (mkBag "x" 1) (mkBag "y" 1))

  Node emptyset = d_nodeManager->mkConst(
      EmptySet(d_nodeManager->mkSetType(d_nodeManager->stringType())));
  Node emptybag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node input1 = d_nodeManager->mkNode(BAG_FROM_SET, emptyset);
  Node output1 = emptybag;
  ASSERT_EQ(output1, NormalForm::evaluate(input1));

  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));

  Node xSingleton = d_nodeManager->mkSingleton(d_nodeManager->stringType(), x);
  Node ySingleton = d_nodeManager->mkSingleton(d_nodeManager->stringType(), y);

  Node x_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(1)));
  Node y_1 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(1)));

  Node input2 = d_nodeManager->mkNode(BAG_FROM_SET, xSingleton);
  Node output2 = x_1;
  ASSERT_EQ(output2, NormalForm::evaluate(input2));

  // for normal sets, the first node is the largest, not smallest
  Node normalSet = d_nodeManager->mkNode(UNION, ySingleton, xSingleton);
  Node input3 = d_nodeManager->mkNode(BAG_FROM_SET, normalSet);
  Node output3 = d_nodeManager->mkNode(UNION_DISJOINT, x_1, y_1);
  ASSERT_EQ(output3, NormalForm::evaluate(input3));
}

TEST_F(TestTheoryWhiteBagsNormalForm, to_set)
{
  // Examples
  // --------
  //  - (bag.to_set (emptybag String)) = (emptyset String)
  //  - (bag.to_set (mkBag "x" 4)) = (singleton "x")
  //  - (bag.to_set (disjoint_union (mkBag "x" 3) (mkBag "y" 5)) =
  //     (union (singleton "x") (singleton "y")))

  Node emptyset = d_nodeManager->mkConst(
      EmptySet(d_nodeManager->mkSetType(d_nodeManager->stringType())));
  Node emptybag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node input1 = d_nodeManager->mkNode(BAG_TO_SET, emptybag);
  Node output1 = emptyset;
  ASSERT_EQ(output1, NormalForm::evaluate(input1));

  Node x = d_nodeManager->mkConst(String("x"));
  Node y = d_nodeManager->mkConst(String("y"));

  Node xSingleton = d_nodeManager->mkSingleton(d_nodeManager->stringType(), x);
  Node ySingleton = d_nodeManager->mkSingleton(d_nodeManager->stringType(), y);

  Node x_4 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(4)));
  Node y_5 = d_nodeManager->mkBag(
      d_nodeManager->stringType(), y, d_nodeManager->mkConst(Rational(5)));

  Node input2 = d_nodeManager->mkNode(BAG_TO_SET, x_4);
  Node output2 = xSingleton;
  ASSERT_EQ(output2, NormalForm::evaluate(input2));

  // for normal sets, the first node is the largest, not smallest
  Node normalBag = d_nodeManager->mkNode(UNION_DISJOINT, x_4, y_5);
  Node input3 = d_nodeManager->mkNode(BAG_TO_SET, normalBag);
  Node output3 = d_nodeManager->mkNode(UNION, ySingleton, xSingleton);
  ASSERT_EQ(output3, NormalForm::evaluate(input3));
}
}  // namespace test
}  // namespace cvc5
