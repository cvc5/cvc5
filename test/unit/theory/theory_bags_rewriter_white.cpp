/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of bags rewriter
 */

#include "expr/dtype.h"
#include "test_smt.h"
#include "theory/bags/bags_rewriter.h"
#include "theory/strings/type_enumerator.h"

namespace cvc5 {

using namespace theory;
using namespace kind;
using namespace theory::bags;

namespace test {

typedef expr::Attribute<Node, Node> attribute;

class TestTheoryWhiteBagsRewriter : public TestSmt
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
    for (size_t i = 0; i < n; i++)
    {
      elements[i] =
          d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
    }
    return elements;
  }

  std::unique_ptr<BagsRewriter> d_rewriter;
};

TEST_F(TestTheoryWhiteBagsRewriter, empty_bag_normal_form)
{
  Node emptybag = d_nodeManager->mkConst(EmptyBag(d_nodeManager->stringType()));
  // empty bags are in normal form
  ASSERT_TRUE(emptybag.isConst());
  RewriteResponse response = d_rewriter->postRewrite(emptybag);
  ASSERT_TRUE(emptybag == response.d_node && response.d_status == REWRITE_DONE);
}

TEST_F(TestTheoryWhiteBagsRewriter, bag_equality)
{
  std::vector<Node> elements = getNStrings(2);
  Node x = elements[0];
  Node y = elements[1];
  Node c = d_skolemManager->mkDummySkolem("c", d_nodeManager->integerType());
  Node d = d_skolemManager->mkDummySkolem("d", d_nodeManager->integerType());
  Node A = d_nodeManager->mkBag(d_nodeManager->stringType(), x, c);
  Node B = d_nodeManager->mkBag(d_nodeManager->stringType(), y, d);
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node emptyString = d_nodeManager->mkConst(String(""));
  Node constantBag = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                          emptyString,
                                          d_nodeManager->mkConst(Rational(1)));

  // (= A A) = true where A is a bag
  Node n1 = A.eqNode(A);
  RewriteResponse response1 = d_rewriter->preRewrite(n1);
  ASSERT_TRUE(response1.d_node == d_nodeManager->mkConst(true)
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (= A B) = false if A and B are different bag constants
  Node n2 = constantBag.eqNode(emptyBag);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_node == d_nodeManager->mkConst(false)
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (= B A) = (= A B) if A < B and at least one of A or B is not a constant
  Node n3 = B.eqNode(A);
  RewriteResponse response3 = d_rewriter->postRewrite(n3);
  ASSERT_TRUE(response3.d_node == A.eqNode(B)
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (= A B) = (= A B) no rewrite
  Node n4 = A.eqNode(B);
  RewriteResponse response4 = d_rewriter->postRewrite(n4);
  ASSERT_TRUE(response4.d_node == n4 && response4.d_status == REWRITE_DONE);
}

TEST_F(TestTheoryWhiteBagsRewriter, mkBag_constant_element)
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
  RewriteResponse negativeResponse = d_rewriter->postRewrite(negative);
  RewriteResponse zeroResponse = d_rewriter->postRewrite(zero);
  RewriteResponse positiveResponse = d_rewriter->postRewrite(positive);

  // bags with non-positive multiplicity are rewritten as empty bags
  ASSERT_TRUE(negativeResponse.d_status == REWRITE_AGAIN_FULL
              && negativeResponse.d_node == emptybag);
  ASSERT_TRUE(zeroResponse.d_status == REWRITE_AGAIN_FULL
              && zeroResponse.d_node == emptybag);

  // no change for positive
  ASSERT_TRUE(positiveResponse.d_status == REWRITE_DONE
              && positive == positiveResponse.d_node);
}

TEST_F(TestTheoryWhiteBagsRewriter, mkBag_variable_element)
{
  Node skolem =
      d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node variable = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                       skolem,
                                       d_nodeManager->mkConst(Rational(-1)));
  Node negative = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                       skolem,
                                       d_nodeManager->mkConst(Rational(-1)));
  Node zero = d_nodeManager->mkBag(
      d_nodeManager->stringType(), skolem, d_nodeManager->mkConst(Rational(0)));
  Node positive = d_nodeManager->mkBag(
      d_nodeManager->stringType(), skolem, d_nodeManager->mkConst(Rational(1)));
  Node emptybag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  RewriteResponse negativeResponse = d_rewriter->postRewrite(negative);
  RewriteResponse zeroResponse = d_rewriter->postRewrite(zero);
  RewriteResponse positiveResponse = d_rewriter->postRewrite(positive);

  // bags with non-positive multiplicity are rewritten as empty bags
  ASSERT_TRUE(negativeResponse.d_status == REWRITE_AGAIN_FULL
              && negativeResponse.d_node == emptybag);
  ASSERT_TRUE(zeroResponse.d_status == REWRITE_AGAIN_FULL
              && zeroResponse.d_node == emptybag);

  // no change for positive
  ASSERT_TRUE(positiveResponse.d_status == REWRITE_DONE
              && positive == positiveResponse.d_node);
}

TEST_F(TestTheoryWhiteBagsRewriter, bag_count)
{
  int n = 3;
  Node skolem =
      d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(skolem.getType())));
  Node bag = d_nodeManager->mkBag(
      d_nodeManager->stringType(), skolem, d_nodeManager->mkConst(Rational(n)));

  // (bag.count x emptybag) = 0
  Node n1 = d_nodeManager->mkNode(BAG_COUNT, skolem, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_status == REWRITE_AGAIN_FULL
              && response1.d_node == d_nodeManager->mkConst(Rational(0)));

  // (bag.count x (mkBag x c) = c where c > 0 is a constant
  Node n2 = d_nodeManager->mkNode(BAG_COUNT, skolem, bag);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_status == REWRITE_AGAIN_FULL
              && response2.d_node == d_nodeManager->mkConst(Rational(n)));
}

TEST_F(TestTheoryWhiteBagsRewriter, duplicate_removal)
{
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node bag = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(5)));

  // (duplicate_removal (mkBag x n)) = (mkBag x 1)
  Node n = d_nodeManager->mkNode(DUPLICATE_REMOVAL, bag);
  RewriteResponse response = d_rewriter->postRewrite(n);
  Node noDuplicate = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(1)));
  ASSERT_TRUE(response.d_node == noDuplicate
              && response.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, union_max)
{
  int n = 3;
  std::vector<Node> elements = getNStrings(2);
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node A = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[0],
                                d_nodeManager->mkConst(Rational(n)));
  Node B = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[1],
                                d_nodeManager->mkConst(Rational(n + 1)));
  Node unionMaxAB = d_nodeManager->mkNode(UNION_MAX, A, B);
  Node unionMaxBA = d_nodeManager->mkNode(UNION_MAX, B, A);
  Node unionDisjointAB = d_nodeManager->mkNode(UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(UNION_DISJOINT, B, A);

  // (union_max A emptybag) = A
  Node unionMax1 = d_nodeManager->mkNode(UNION_MAX, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(unionMax1);
  ASSERT_TRUE(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (union_max emptybag A) = A
  Node unionMax2 = d_nodeManager->mkNode(UNION_MAX, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(unionMax2);
  ASSERT_TRUE(response2.d_node == A
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (union_max A A) = A
  Node unionMax3 = d_nodeManager->mkNode(UNION_MAX, A, A);
  RewriteResponse response3 = d_rewriter->postRewrite(unionMax3);
  ASSERT_TRUE(response3.d_node == A
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (union_max A (union_max A B)) = (union_max A B)
  Node unionMax4 = d_nodeManager->mkNode(UNION_MAX, A, unionMaxAB);
  RewriteResponse response4 = d_rewriter->postRewrite(unionMax4);
  ASSERT_TRUE(response4.d_node == unionMaxAB
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (union_max A (union_max B A)) = (union_max B A)
  Node unionMax5 = d_nodeManager->mkNode(UNION_MAX, A, unionMaxBA);
  RewriteResponse response5 = d_rewriter->postRewrite(unionMax5);
  ASSERT_TRUE(response5.d_node == unionMaxBA
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (union_max (union_max A B) A) = (union_max A B)
  Node unionMax6 = d_nodeManager->mkNode(UNION_MAX, unionMaxAB, A);
  RewriteResponse response6 = d_rewriter->postRewrite(unionMax6);
  ASSERT_TRUE(response6.d_node == unionMaxAB
              && response6.d_status == REWRITE_AGAIN_FULL);

  // (union_max (union_max B A) A) = (union_max B A)
  Node unionMax7 = d_nodeManager->mkNode(UNION_MAX, unionMaxBA, A);
  RewriteResponse response7 = d_rewriter->postRewrite(unionMax7);
  ASSERT_TRUE(response7.d_node == unionMaxBA
              && response7.d_status == REWRITE_AGAIN_FULL);

  // (union_max A (union_disjoint A B)) = (union_disjoint A B)
  Node unionMax8 = d_nodeManager->mkNode(UNION_MAX, A, unionDisjointAB);
  RewriteResponse response8 = d_rewriter->postRewrite(unionMax8);
  ASSERT_TRUE(response8.d_node == unionDisjointAB
              && response8.d_status == REWRITE_AGAIN_FULL);

  // (union_max A (union_disjoint B A)) = (union_disjoint B A)
  Node unionMax9 = d_nodeManager->mkNode(UNION_MAX, A, unionDisjointBA);
  RewriteResponse response9 = d_rewriter->postRewrite(unionMax9);
  ASSERT_TRUE(response9.d_node == unionDisjointBA
              && response9.d_status == REWRITE_AGAIN_FULL);

  // (union_max (union_disjoint A B) A) = (union_disjoint A B)
  Node unionMax10 = d_nodeManager->mkNode(UNION_MAX, unionDisjointAB, A);
  RewriteResponse response10 = d_rewriter->postRewrite(unionMax10);
  ASSERT_TRUE(response10.d_node == unionDisjointAB
              && response10.d_status == REWRITE_AGAIN_FULL);

  // (union_max (union_disjoint B A) A) = (union_disjoint B A)
  Node unionMax11 = d_nodeManager->mkNode(UNION_MAX, unionDisjointBA, A);
  RewriteResponse response11 = d_rewriter->postRewrite(unionMax11);
  ASSERT_TRUE(response11.d_node == unionDisjointBA
              && response11.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, union_disjoint)
{
  int n = 3;
  std::vector<Node> elements = getNStrings(3);
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node A = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[0],
                                d_nodeManager->mkConst(Rational(n)));
  Node B = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[1],
                                d_nodeManager->mkConst(Rational(n + 1)));
  Node C = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[2],
                                d_nodeManager->mkConst(Rational(n + 2)));

  Node unionDisjointAB = d_nodeManager->mkNode(UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(UNION_DISJOINT, B, A);
  Node unionMaxAB = d_nodeManager->mkNode(UNION_MAX, A, B);
  Node unionMaxAC = d_nodeManager->mkNode(UNION_MAX, A, C);
  Node unionMaxBA = d_nodeManager->mkNode(UNION_MAX, B, A);
  Node intersectionAB = d_nodeManager->mkNode(INTERSECTION_MIN, A, B);
  Node intersectionBA = d_nodeManager->mkNode(INTERSECTION_MIN, B, A);

  // (union_disjoint A emptybag) = A
  Node unionDisjoint1 = d_nodeManager->mkNode(UNION_DISJOINT, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(unionDisjoint1);
  ASSERT_TRUE(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (union_disjoint emptybag A) = A
  Node unionDisjoint2 = d_nodeManager->mkNode(UNION_DISJOINT, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(unionDisjoint2);
  ASSERT_TRUE(response2.d_node == A
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (union_disjoint (union_max A B) (intersection_min B A)) =
  //          (union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
  Node unionDisjoint3 =
      d_nodeManager->mkNode(UNION_DISJOINT, unionMaxAB, intersectionBA);
  RewriteResponse response3 = d_rewriter->postRewrite(unionDisjoint3);
  ASSERT_TRUE(response3.d_node == unionDisjointAB
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (union_disjoint (intersection_min B A)) (union_max A B) =
  //          (union_disjoint B A) // sum(a,b) = max(a,b) + min(a,b)
  Node unionDisjoint4 =
      d_nodeManager->mkNode(UNION_DISJOINT, unionMaxBA, intersectionBA);
  RewriteResponse response4 = d_rewriter->postRewrite(unionDisjoint4);
  ASSERT_TRUE(response4.d_node == unionDisjointBA
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (union_disjoint (intersection_min B A)) (union_max A B) =
  //          (union_disjoint B A) // sum(a,b) = max(a,b) + min(a,b)
  Node unionDisjoint5 =
      d_nodeManager->mkNode(UNION_DISJOINT, unionMaxAC, intersectionAB);
  RewriteResponse response5 = d_rewriter->postRewrite(unionDisjoint5);
  ASSERT_TRUE(response5.d_node == unionDisjoint5
              && response5.d_status == REWRITE_DONE);
}

TEST_F(TestTheoryWhiteBagsRewriter, intersection_min)
{
  int n = 3;
  std::vector<Node> elements = getNStrings(2);
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node A = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[0],
                                d_nodeManager->mkConst(Rational(n)));
  Node B = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[1],
                                d_nodeManager->mkConst(Rational(n + 1)));
  Node unionMaxAB = d_nodeManager->mkNode(UNION_MAX, A, B);
  Node unionMaxBA = d_nodeManager->mkNode(UNION_MAX, B, A);
  Node unionDisjointAB = d_nodeManager->mkNode(UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(UNION_DISJOINT, B, A);

  // (intersection_min A emptybag) = emptyBag
  Node n1 = d_nodeManager->mkNode(INTERSECTION_MIN, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == emptyBag
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min emptybag A) = emptyBag
  Node n2 = d_nodeManager->mkNode(INTERSECTION_MIN, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_node == emptyBag
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min A A) = A
  Node n3 = d_nodeManager->mkNode(INTERSECTION_MIN, A, A);
  RewriteResponse response3 = d_rewriter->postRewrite(n3);
  ASSERT_TRUE(response3.d_node == A
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min A (union_max A B) = A
  Node n4 = d_nodeManager->mkNode(INTERSECTION_MIN, A, unionMaxAB);
  RewriteResponse response4 = d_rewriter->postRewrite(n4);
  ASSERT_TRUE(response4.d_node == A
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min A (union_max B A) = A
  Node n5 = d_nodeManager->mkNode(INTERSECTION_MIN, A, unionMaxBA);
  RewriteResponse response5 = d_rewriter->postRewrite(n5);
  ASSERT_TRUE(response5.d_node == A
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min (union_max A B) A) = A
  Node n6 = d_nodeManager->mkNode(INTERSECTION_MIN, unionMaxAB, A);
  RewriteResponse response6 = d_rewriter->postRewrite(n6);
  ASSERT_TRUE(response6.d_node == A
              && response6.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min (union_max B A) A) = A
  Node n7 = d_nodeManager->mkNode(INTERSECTION_MIN, unionMaxBA, A);
  RewriteResponse response7 = d_rewriter->postRewrite(n7);
  ASSERT_TRUE(response7.d_node == A
              && response7.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min A (union_disjoint A B) = A
  Node n8 = d_nodeManager->mkNode(INTERSECTION_MIN, A, unionDisjointAB);
  RewriteResponse response8 = d_rewriter->postRewrite(n8);
  ASSERT_TRUE(response8.d_node == A
              && response8.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min A (union_disjoint B A) = A
  Node n9 = d_nodeManager->mkNode(INTERSECTION_MIN, A, unionDisjointBA);
  RewriteResponse response9 = d_rewriter->postRewrite(n9);
  ASSERT_TRUE(response9.d_node == A
              && response9.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min (union_disjoint A B) A) = A
  Node n10 = d_nodeManager->mkNode(INTERSECTION_MIN, unionDisjointAB, A);
  RewriteResponse response10 = d_rewriter->postRewrite(n10);
  ASSERT_TRUE(response10.d_node == A
              && response10.d_status == REWRITE_AGAIN_FULL);

  // (intersection_min (union_disjoint B A) A) = A
  Node n11 = d_nodeManager->mkNode(INTERSECTION_MIN, unionDisjointBA, A);
  RewriteResponse response11 = d_rewriter->postRewrite(n11);
  ASSERT_TRUE(response11.d_node == A
              && response11.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, difference_subtract)
{
  int n = 3;
  std::vector<Node> elements = getNStrings(2);
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node A = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[0],
                                d_nodeManager->mkConst(Rational(n)));
  Node B = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[1],
                                d_nodeManager->mkConst(Rational(n + 1)));
  Node unionMaxAB = d_nodeManager->mkNode(UNION_MAX, A, B);
  Node unionMaxBA = d_nodeManager->mkNode(UNION_MAX, B, A);
  Node unionDisjointAB = d_nodeManager->mkNode(UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(UNION_DISJOINT, B, A);
  Node intersectionAB = d_nodeManager->mkNode(INTERSECTION_MIN, A, B);
  Node intersectionBA = d_nodeManager->mkNode(INTERSECTION_MIN, B, A);

  // (difference_subtract A emptybag) = A
  Node n1 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract emptybag A) = emptyBag
  Node n2 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_node == emptyBag
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract A A) = emptybag
  Node n3 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, A, A);
  RewriteResponse response3 = d_rewriter->postRewrite(n3);
  ASSERT_TRUE(response3.d_node == emptyBag
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract (union_disjoint A B) A) = B
  Node n4 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, unionDisjointAB, A);
  RewriteResponse response4 = d_rewriter->postRewrite(n4);
  ASSERT_TRUE(response4.d_node == B
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract (union_disjoint B A) A) = B
  Node n5 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, unionDisjointBA, A);
  RewriteResponse response5 = d_rewriter->postRewrite(n5);
  ASSERT_TRUE(response5.d_node == B
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract A (union_disjoint A B)) = emptybag
  Node n6 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, A, unionDisjointAB);
  RewriteResponse response6 = d_rewriter->postRewrite(n6);
  ASSERT_TRUE(response6.d_node == emptyBag
              && response6.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract A (union_disjoint B A)) = emptybag
  Node n7 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, A, unionDisjointBA);
  RewriteResponse response7 = d_rewriter->postRewrite(n7);
  ASSERT_TRUE(response7.d_node == emptyBag
              && response7.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract A (union_max A B)) = emptybag
  Node n8 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, A, unionMaxAB);
  RewriteResponse response8 = d_rewriter->postRewrite(n8);
  ASSERT_TRUE(response8.d_node == emptyBag
              && response8.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract A (union_max B A)) = emptybag
  Node n9 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, A, unionMaxBA);
  RewriteResponse response9 = d_rewriter->postRewrite(n9);
  ASSERT_TRUE(response9.d_node == emptyBag
              && response9.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract (intersection_min A B) A) = emptybag
  Node n10 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, intersectionAB, A);
  RewriteResponse response10 = d_rewriter->postRewrite(n10);
  ASSERT_TRUE(response10.d_node == emptyBag
              && response10.d_status == REWRITE_AGAIN_FULL);

  // (difference_subtract (intersection_min B A) A) = emptybag
  Node n11 = d_nodeManager->mkNode(DIFFERENCE_SUBTRACT, intersectionBA, A);
  RewriteResponse response11 = d_rewriter->postRewrite(n11);
  ASSERT_TRUE(response11.d_node == emptyBag
              && response11.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, difference_remove)
{
  int n = 3;
  std::vector<Node> elements = getNStrings(2);
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node A = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[0],
                                d_nodeManager->mkConst(Rational(n)));
  Node B = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[1],
                                d_nodeManager->mkConst(Rational(n + 1)));
  Node unionMaxAB = d_nodeManager->mkNode(UNION_MAX, A, B);
  Node unionMaxBA = d_nodeManager->mkNode(UNION_MAX, B, A);
  Node unionDisjointAB = d_nodeManager->mkNode(UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(UNION_DISJOINT, B, A);
  Node intersectionAB = d_nodeManager->mkNode(INTERSECTION_MIN, A, B);
  Node intersectionBA = d_nodeManager->mkNode(INTERSECTION_MIN, B, A);

  // (difference_remove A emptybag) = A
  Node n1 = d_nodeManager->mkNode(DIFFERENCE_REMOVE, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (difference_remove emptybag A) = emptyBag
  Node n2 = d_nodeManager->mkNode(DIFFERENCE_REMOVE, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_node == emptyBag
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (difference_remove A A) = emptybag
  Node n3 = d_nodeManager->mkNode(DIFFERENCE_REMOVE, A, A);
  RewriteResponse response3 = d_rewriter->postRewrite(n3);
  ASSERT_TRUE(response3.d_node == emptyBag
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (difference_remove A (union_disjoint A B)) = emptybag
  Node n6 = d_nodeManager->mkNode(DIFFERENCE_REMOVE, A, unionDisjointAB);
  RewriteResponse response6 = d_rewriter->postRewrite(n6);
  ASSERT_TRUE(response6.d_node == emptyBag
              && response6.d_status == REWRITE_AGAIN_FULL);

  // (difference_remove A (union_disjoint B A)) = emptybag
  Node n7 = d_nodeManager->mkNode(DIFFERENCE_REMOVE, A, unionDisjointBA);
  RewriteResponse response7 = d_rewriter->postRewrite(n7);
  ASSERT_TRUE(response7.d_node == emptyBag
              && response7.d_status == REWRITE_AGAIN_FULL);

  // (difference_remove A (union_max A B)) = emptybag
  Node n8 = d_nodeManager->mkNode(DIFFERENCE_REMOVE, A, unionMaxAB);
  RewriteResponse response8 = d_rewriter->postRewrite(n8);
  ASSERT_TRUE(response8.d_node == emptyBag
              && response8.d_status == REWRITE_AGAIN_FULL);

  // (difference_remove A (union_max B A)) = emptybag
  Node n9 = d_nodeManager->mkNode(DIFFERENCE_REMOVE, A, unionMaxBA);
  RewriteResponse response9 = d_rewriter->postRewrite(n9);
  ASSERT_TRUE(response9.d_node == emptyBag
              && response9.d_status == REWRITE_AGAIN_FULL);

  // (difference_remove (intersection_min A B) A) = emptybag
  Node n10 = d_nodeManager->mkNode(DIFFERENCE_REMOVE, intersectionAB, A);
  RewriteResponse response10 = d_rewriter->postRewrite(n10);
  ASSERT_TRUE(response10.d_node == emptyBag
              && response10.d_status == REWRITE_AGAIN_FULL);

  // (difference_remove (intersection_min B A) A) = emptybag
  Node n11 = d_nodeManager->mkNode(DIFFERENCE_REMOVE, intersectionBA, A);
  RewriteResponse response11 = d_rewriter->postRewrite(n11);
  ASSERT_TRUE(response11.d_node == emptyBag
              && response11.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, choose)
{
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node c = d_nodeManager->mkConst(Rational(3));
  Node bag = d_nodeManager->mkBag(d_nodeManager->stringType(), x, c);

  // (bag.choose (mkBag x c)) = x where c is a constant > 0
  Node n1 = d_nodeManager->mkNode(BAG_CHOOSE, bag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == x
              && response1.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, bag_card)
{
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node zero = d_nodeManager->mkConst(Rational(0));
  Node c = d_nodeManager->mkConst(Rational(3));
  Node bag = d_nodeManager->mkBag(d_nodeManager->stringType(), x, c);
  std::vector<Node> elements = getNStrings(2);
  Node A = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[0],
                                d_nodeManager->mkConst(Rational(4)));
  Node B = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                elements[1],
                                d_nodeManager->mkConst(Rational(5)));
  Node unionDisjointAB = d_nodeManager->mkNode(UNION_DISJOINT, A, B);

  // TODO(projects#223): enable this test after implementing bags normal form
  //    // (bag.card emptybag) = 0
  //    Node n1 = d_nodeManager->mkNode(BAG_CARD, emptyBag);
  //    RewriteResponse response1 = d_rewriter->postRewrite(n1);
  //    ASSERT_TRUE(response1.d_node == zero && response1.d_status ==
  //    REWRITE_AGAIN_FULL);

  // (bag.card (mkBag x c)) = c where c is a constant > 0
  Node n2 = d_nodeManager->mkNode(BAG_CARD, bag);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_node == c
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (bag.card (union-disjoint A B)) = (+ (bag.card A) (bag.card B))
  Node n3 = d_nodeManager->mkNode(BAG_CARD, unionDisjointAB);
  Node cardA = d_nodeManager->mkNode(BAG_CARD, A);
  Node cardB = d_nodeManager->mkNode(BAG_CARD, B);
  Node plus = d_nodeManager->mkNode(PLUS, cardA, cardB);
  RewriteResponse response3 = d_rewriter->postRewrite(n3);
  ASSERT_TRUE(response3.d_node == plus
              && response3.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, is_singleton)
{
  Node emptybag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node c = d_skolemManager->mkDummySkolem("c", d_nodeManager->integerType());
  Node bag = d_nodeManager->mkBag(d_nodeManager->stringType(), x, c);

  // TODO(projects#223): complete this function
  // (bag.is_singleton emptybag) = false
  //    Node n1 = d_nodeManager->mkNode(BAG_IS_SINGLETON, emptybag);
  //    RewriteResponse response1 = d_rewriter->postRewrite(n1);
  //    ASSERT_TRUE(response1.d_node == d_nodeManager->mkConst(false)
  //              && response1.d_status == REWRITE_AGAIN_FULL);

  // (bag.is_singleton (mkBag x c) = (c == 1)
  Node n2 = d_nodeManager->mkNode(BAG_IS_SINGLETON, bag);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  Node one = d_nodeManager->mkConst(Rational(1));
  Node equal = c.eqNode(one);
  ASSERT_TRUE(response2.d_node == equal
              && response2.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, from_set)
{
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node singleton = d_nodeManager->mkSingleton(d_nodeManager->stringType(), x);

  // (bag.from_set (singleton (singleton_op Int) x)) = (mkBag x 1)
  Node n = d_nodeManager->mkNode(BAG_FROM_SET, singleton);
  RewriteResponse response = d_rewriter->postRewrite(n);
  Node one = d_nodeManager->mkConst(Rational(1));
  Node bag = d_nodeManager->mkBag(d_nodeManager->stringType(), x, one);
  ASSERT_TRUE(response.d_node == bag
              && response.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, to_set)
{
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node bag = d_nodeManager->mkBag(
      d_nodeManager->stringType(), x, d_nodeManager->mkConst(Rational(5)));

  // (bag.to_set (mkBag x n)) = (singleton (singleton_op T) x)
  Node n = d_nodeManager->mkNode(BAG_TO_SET, bag);
  RewriteResponse response = d_rewriter->postRewrite(n);
  Node singleton = d_nodeManager->mkSingleton(d_nodeManager->stringType(), x);
  ASSERT_TRUE(response.d_node == singleton
              && response.d_status == REWRITE_AGAIN_FULL);
}
}  // namespace test
}  // namespace cvc5
