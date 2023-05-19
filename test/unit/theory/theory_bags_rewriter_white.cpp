/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of bags rewriter
 */

#include "expr/dtype.h"
#include "expr/emptybag.h"
#include "test_smt.h"
#include "theory/bags/bags_rewriter.h"
#include "theory/strings/type_enumerator.h"
#include "util/rational.h"
#include "util/string.h"

namespace cvc5::internal {

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
  Node A = d_nodeManager->mkNode(BAG_MAKE, x, c);
  Node B = d_nodeManager->mkNode(BAG_MAKE, y, d);
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node emptyString = d_nodeManager->mkConst(String(""));
  Node constantBag = d_nodeManager->mkNode(
      BAG_MAKE, emptyString, d_nodeManager->mkConstInt(Rational(1)));

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
  Node negative = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(-1)));
  Node zero = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(0)));
  Node positive = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(1)));
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
  Node variable = d_nodeManager->mkNode(
      BAG_MAKE, skolem, d_nodeManager->mkConstInt(Rational(-1)));
  Node negative = d_nodeManager->mkNode(
      BAG_MAKE, skolem, d_nodeManager->mkConstInt(Rational(-1)));
  Node zero = d_nodeManager->mkNode(
      BAG_MAKE, skolem, d_nodeManager->mkConstInt(Rational(0)));
  Node positive = d_nodeManager->mkNode(
      BAG_MAKE, skolem, d_nodeManager->mkConstInt(Rational(1)));
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
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node three = d_nodeManager->mkConstInt(Rational(3));
  Node skolem =
      d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(skolem.getType())));

  // (bag.count x (as bag.empty (Bag String))) = 0
  Node n1 = d_nodeManager->mkNode(BAG_COUNT, skolem, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_status == REWRITE_AGAIN_FULL
              && response1.d_node == zero);

  // (bag.count x (bag x c) = c, c > 0 is a constant
  Node bag = d_nodeManager->mkNode(BAG_MAKE, skolem, three);
  Node n2 = d_nodeManager->mkNode(BAG_COUNT, skolem, bag);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);

  Node geq = d_nodeManager->mkNode(GEQ, three, one);
  Node ite = d_nodeManager->mkNode(ITE, geq, three, zero);
  ASSERT_TRUE(response2.d_status == REWRITE_AGAIN_FULL
              && response2.d_node == three);
}

TEST_F(TestTheoryWhiteBagsRewriter, duplicate_removal)
{
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node bag = d_nodeManager->mkNode(
      BAG_MAKE, x, d_nodeManager->mkConstInt(Rational(5)));

  // (bag.duplicate_removal (bag x n)) = (bag x 1)
  Node n = d_nodeManager->mkNode(BAG_DUPLICATE_REMOVAL, bag);
  RewriteResponse response = d_rewriter->postRewrite(n);
  Node noDuplicate = d_nodeManager->mkNode(
      BAG_MAKE, x, d_nodeManager->mkConstInt(Rational(1)));
  ASSERT_TRUE(response.d_node == noDuplicate
              && response.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, union_max)
{
  int n = 3;
  std::vector<Node> elements = getNStrings(2);
  Node emptyBag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node A = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(n)));
  Node B = d_nodeManager->mkNode(
      BAG_MAKE, elements[1], d_nodeManager->mkConstInt(Rational(n + 1)));
  Node unionMaxAB = d_nodeManager->mkNode(BAG_UNION_MAX, A, B);
  Node unionMaxBA = d_nodeManager->mkNode(BAG_UNION_MAX, B, A);
  Node unionDisjointAB = d_nodeManager->mkNode(BAG_UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(BAG_UNION_DISJOINT, B, A);

  // (bag.union_max A (as bag.empty (Bag String))) = A
  Node unionMax1 = d_nodeManager->mkNode(BAG_UNION_MAX, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(unionMax1);
  ASSERT_TRUE(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max (as bag.empty (Bag String)) A) = A
  Node unionMax2 = d_nodeManager->mkNode(BAG_UNION_MAX, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(unionMax2);
  ASSERT_TRUE(response2.d_node == A
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max A A) = A
  Node unionMax3 = d_nodeManager->mkNode(BAG_UNION_MAX, A, A);
  RewriteResponse response3 = d_rewriter->postRewrite(unionMax3);
  ASSERT_TRUE(response3.d_node == A
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max A (bag.union_max A B)) = (bag.union_max A B)
  Node unionMax4 = d_nodeManager->mkNode(BAG_UNION_MAX, A, unionMaxAB);
  RewriteResponse response4 = d_rewriter->postRewrite(unionMax4);
  ASSERT_TRUE(response4.d_node == unionMaxAB
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max A (bag.union_max B A)) = (bag.union_max B A)
  Node unionMax5 = d_nodeManager->mkNode(BAG_UNION_MAX, A, unionMaxBA);
  RewriteResponse response5 = d_rewriter->postRewrite(unionMax5);
  ASSERT_TRUE(response5.d_node == unionMaxBA
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max (bag.union_max A B) A) = (bag.union_max A B)
  Node unionMax6 = d_nodeManager->mkNode(BAG_UNION_MAX, unionMaxAB, A);
  RewriteResponse response6 = d_rewriter->postRewrite(unionMax6);
  ASSERT_TRUE(response6.d_node == unionMaxAB
              && response6.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max (bag.union_max B A) A) = (bag.union_max B A)
  Node unionMax7 = d_nodeManager->mkNode(BAG_UNION_MAX, unionMaxBA, A);
  RewriteResponse response7 = d_rewriter->postRewrite(unionMax7);
  ASSERT_TRUE(response7.d_node == unionMaxBA
              && response7.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max A (bag.union_disjoint A B)) = (bag.union_disjoint A B)
  Node unionMax8 = d_nodeManager->mkNode(BAG_UNION_MAX, A, unionDisjointAB);
  RewriteResponse response8 = d_rewriter->postRewrite(unionMax8);
  ASSERT_TRUE(response8.d_node == unionDisjointAB
              && response8.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max A (bag.union_disjoint B A)) = (bag.union_disjoint B A)
  Node unionMax9 = d_nodeManager->mkNode(BAG_UNION_MAX, A, unionDisjointBA);
  RewriteResponse response9 = d_rewriter->postRewrite(unionMax9);
  ASSERT_TRUE(response9.d_node == unionDisjointBA
              && response9.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max (bag.union_disjoint A B) A) = (bag.union_disjoint A B)
  Node unionMax10 = d_nodeManager->mkNode(BAG_UNION_MAX, unionDisjointAB, A);
  RewriteResponse response10 = d_rewriter->postRewrite(unionMax10);
  ASSERT_TRUE(response10.d_node == unionDisjointAB
              && response10.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_max (bag.union_disjoint B A) A) = (bag.union_disjoint B A)
  Node unionMax11 = d_nodeManager->mkNode(BAG_UNION_MAX, unionDisjointBA, A);
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
  Node A = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(n)));
  Node B = d_nodeManager->mkNode(
      BAG_MAKE, elements[1], d_nodeManager->mkConstInt(Rational(n + 1)));
  Node C = d_nodeManager->mkNode(
      BAG_MAKE, elements[2], d_nodeManager->mkConstInt(Rational(n + 2)));

  Node unionDisjointAB = d_nodeManager->mkNode(BAG_UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(BAG_UNION_DISJOINT, B, A);
  Node unionMaxAB = d_nodeManager->mkNode(BAG_UNION_MAX, A, B);
  Node unionMaxAC = d_nodeManager->mkNode(BAG_UNION_MAX, A, C);
  Node unionMaxBA = d_nodeManager->mkNode(BAG_UNION_MAX, B, A);
  Node intersectionAB = d_nodeManager->mkNode(BAG_INTER_MIN, A, B);
  Node intersectionBA = d_nodeManager->mkNode(BAG_INTER_MIN, B, A);

  // (bag.union_disjoint A (as bag.empty (Bag String))) = A
  Node unionDisjoint1 = d_nodeManager->mkNode(BAG_UNION_DISJOINT, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(unionDisjoint1);
  ASSERT_TRUE(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_disjoint (as bag.empty (Bag String)) A) = A
  Node unionDisjoint2 = d_nodeManager->mkNode(BAG_UNION_DISJOINT, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(unionDisjoint2);
  ASSERT_TRUE(response2.d_node == A
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_disjoint (bag.union_max A B) (bag.inter_min B A)) =
  //          (bag.union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
  Node unionDisjoint3 =
      d_nodeManager->mkNode(BAG_UNION_DISJOINT, unionMaxAB, intersectionBA);
  RewriteResponse response3 = d_rewriter->postRewrite(unionDisjoint3);
  ASSERT_TRUE(response3.d_node == unionDisjointAB
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_disjoint (bag.inter_min B A)) (bag.union_max A B) =
  //          (bag.union_disjoint B A) // sum(a,b) = max(a,b) + min(a,b)
  Node unionDisjoint4 =
      d_nodeManager->mkNode(BAG_UNION_DISJOINT, unionMaxBA, intersectionBA);
  RewriteResponse response4 = d_rewriter->postRewrite(unionDisjoint4);
  ASSERT_TRUE(response4.d_node == unionDisjointBA
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (bag.union_disjoint (bag.inter_min B A)) (bag.union_max A B) =
  //          (bag.union_disjoint B A) // sum(a,b) = max(a,b) + min(a,b)
  Node unionDisjoint5 =
      d_nodeManager->mkNode(BAG_UNION_DISJOINT, unionMaxAC, intersectionAB);
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
  Node A = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(n)));
  Node B = d_nodeManager->mkNode(
      BAG_MAKE, elements[1], d_nodeManager->mkConstInt(Rational(n + 1)));
  Node unionMaxAB = d_nodeManager->mkNode(BAG_UNION_MAX, A, B);
  Node unionMaxBA = d_nodeManager->mkNode(BAG_UNION_MAX, B, A);
  Node unionDisjointAB = d_nodeManager->mkNode(BAG_UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(BAG_UNION_DISJOINT, B, A);

  // (bag.inter_min A (as bag.empty (Bag String)) =
  // (as bag.empty (Bag String))
  Node n1 = d_nodeManager->mkNode(BAG_INTER_MIN, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == emptyBag
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min (as bag.empty (Bag String)) A) =
  // (as bag.empty (Bag String))
  Node n2 = d_nodeManager->mkNode(BAG_INTER_MIN, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_node == emptyBag
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min A A) = A
  Node n3 = d_nodeManager->mkNode(BAG_INTER_MIN, A, A);
  RewriteResponse response3 = d_rewriter->postRewrite(n3);
  ASSERT_TRUE(response3.d_node == A
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min A (bag.union_max A B) = A
  Node n4 = d_nodeManager->mkNode(BAG_INTER_MIN, A, unionMaxAB);
  RewriteResponse response4 = d_rewriter->postRewrite(n4);
  ASSERT_TRUE(response4.d_node == A
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min A (bag.union_max B A) = A
  Node n5 = d_nodeManager->mkNode(BAG_INTER_MIN, A, unionMaxBA);
  RewriteResponse response5 = d_rewriter->postRewrite(n5);
  ASSERT_TRUE(response5.d_node == A
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min (bag.union_max A B) A) = A
  Node n6 = d_nodeManager->mkNode(BAG_INTER_MIN, unionMaxAB, A);
  RewriteResponse response6 = d_rewriter->postRewrite(n6);
  ASSERT_TRUE(response6.d_node == A
              && response6.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min (bag.union_max B A) A) = A
  Node n7 = d_nodeManager->mkNode(BAG_INTER_MIN, unionMaxBA, A);
  RewriteResponse response7 = d_rewriter->postRewrite(n7);
  ASSERT_TRUE(response7.d_node == A
              && response7.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min A (bag.union_disjoint A B) = A
  Node n8 = d_nodeManager->mkNode(BAG_INTER_MIN, A, unionDisjointAB);
  RewriteResponse response8 = d_rewriter->postRewrite(n8);
  ASSERT_TRUE(response8.d_node == A
              && response8.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min A (bag.union_disjoint B A) = A
  Node n9 = d_nodeManager->mkNode(BAG_INTER_MIN, A, unionDisjointBA);
  RewriteResponse response9 = d_rewriter->postRewrite(n9);
  ASSERT_TRUE(response9.d_node == A
              && response9.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min (bag.union_disjoint A B) A) = A
  Node n10 = d_nodeManager->mkNode(BAG_INTER_MIN, unionDisjointAB, A);
  RewriteResponse response10 = d_rewriter->postRewrite(n10);
  ASSERT_TRUE(response10.d_node == A
              && response10.d_status == REWRITE_AGAIN_FULL);

  // (bag.inter_min (bag.union_disjoint B A) A) = A
  Node n11 = d_nodeManager->mkNode(BAG_INTER_MIN, unionDisjointBA, A);
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
  Node A = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(n)));
  Node B = d_nodeManager->mkNode(
      BAG_MAKE, elements[1], d_nodeManager->mkConstInt(Rational(n + 1)));
  Node unionMaxAB = d_nodeManager->mkNode(BAG_UNION_MAX, A, B);
  Node unionMaxBA = d_nodeManager->mkNode(BAG_UNION_MAX, B, A);
  Node unionDisjointAB = d_nodeManager->mkNode(BAG_UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(BAG_UNION_DISJOINT, B, A);
  Node intersectionAB = d_nodeManager->mkNode(BAG_INTER_MIN, A, B);
  Node intersectionBA = d_nodeManager->mkNode(BAG_INTER_MIN, B, A);

  // (bag.difference_subtract A (as bag.empty (Bag String)) = A
  Node n1 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract (as bag.empty (Bag String)) A) =
  // (as bag.empty (Bag String))
  Node n2 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_node == emptyBag
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract A A) = (as bag.empty (Bag String))
  Node n3 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, A, A);
  RewriteResponse response3 = d_rewriter->postRewrite(n3);
  ASSERT_TRUE(response3.d_node == emptyBag
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract (bag.union_disjoint A B) A) = B
  Node n4 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, unionDisjointAB, A);
  RewriteResponse response4 = d_rewriter->postRewrite(n4);
  ASSERT_TRUE(response4.d_node == B
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract (bag.union_disjoint B A) A) = B
  Node n5 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, unionDisjointBA, A);
  RewriteResponse response5 = d_rewriter->postRewrite(n5);
  ASSERT_TRUE(response5.d_node == B
              && response4.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract A (bag.union_disjoint A B)) =
  // (as bag.empty (Bag String))
  Node n6 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, A, unionDisjointAB);
  RewriteResponse response6 = d_rewriter->postRewrite(n6);
  ASSERT_TRUE(response6.d_node == emptyBag
              && response6.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract A (bag.union_disjoint B A)) =
  // (as bag.empty (Bag String))
  Node n7 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, A, unionDisjointBA);
  RewriteResponse response7 = d_rewriter->postRewrite(n7);
  ASSERT_TRUE(response7.d_node == emptyBag
              && response7.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract A (bag.union_max A B)) =
  // (as bag.empty (Bag String))
  Node n8 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, A, unionMaxAB);
  RewriteResponse response8 = d_rewriter->postRewrite(n8);
  ASSERT_TRUE(response8.d_node == emptyBag
              && response8.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract A (bag.union_max B A)) =
  // (as bag.empty (Bag String))
  Node n9 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, A, unionMaxBA);
  RewriteResponse response9 = d_rewriter->postRewrite(n9);
  ASSERT_TRUE(response9.d_node == emptyBag
              && response9.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract (bag.inter_min A B) A) =
  // (as bag.empty (Bag String))
  Node n10 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, intersectionAB, A);
  RewriteResponse response10 = d_rewriter->postRewrite(n10);
  ASSERT_TRUE(response10.d_node == emptyBag
              && response10.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_subtract (bag.inter_min B A) A) =
  // (as bag.empty (Bag String))
  Node n11 = d_nodeManager->mkNode(BAG_DIFFERENCE_SUBTRACT, intersectionBA, A);
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
  Node A = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(n)));
  Node B = d_nodeManager->mkNode(
      BAG_MAKE, elements[1], d_nodeManager->mkConstInt(Rational(n + 1)));
  Node unionMaxAB = d_nodeManager->mkNode(BAG_UNION_MAX, A, B);
  Node unionMaxBA = d_nodeManager->mkNode(BAG_UNION_MAX, B, A);
  Node unionDisjointAB = d_nodeManager->mkNode(BAG_UNION_DISJOINT, A, B);
  Node unionDisjointBA = d_nodeManager->mkNode(BAG_UNION_DISJOINT, B, A);
  Node intersectionAB = d_nodeManager->mkNode(BAG_INTER_MIN, A, B);
  Node intersectionBA = d_nodeManager->mkNode(BAG_INTER_MIN, B, A);

  // (bag.difference_remove A (as bag.empty (Bag String)) = A
  Node n1 = d_nodeManager->mkNode(BAG_DIFFERENCE_REMOVE, A, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_remove (as bag.empty (Bag String)) A)=
  // (as bag.empty (Bag String))
  Node n2 = d_nodeManager->mkNode(BAG_DIFFERENCE_REMOVE, emptyBag, A);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_node == emptyBag
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_remove A A) = (as bag.empty (Bag String))
  Node n3 = d_nodeManager->mkNode(BAG_DIFFERENCE_REMOVE, A, A);
  RewriteResponse response3 = d_rewriter->postRewrite(n3);
  ASSERT_TRUE(response3.d_node == emptyBag
              && response3.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_remove A (bag.union_disjoint A B)) =
  // (as bag.empty (Bag String))
  Node n6 = d_nodeManager->mkNode(BAG_DIFFERENCE_REMOVE, A, unionDisjointAB);
  RewriteResponse response6 = d_rewriter->postRewrite(n6);
  ASSERT_TRUE(response6.d_node == emptyBag
              && response6.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_remove A (bag.union_disjoint B A)) =
  // (as bag.empty (Bag String))
  Node n7 = d_nodeManager->mkNode(BAG_DIFFERENCE_REMOVE, A, unionDisjointBA);
  RewriteResponse response7 = d_rewriter->postRewrite(n7);
  ASSERT_TRUE(response7.d_node == emptyBag
              && response7.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_remove A (bag.union_max A B)) =
  // (as bag.empty (Bag String))
  Node n8 = d_nodeManager->mkNode(BAG_DIFFERENCE_REMOVE, A, unionMaxAB);
  RewriteResponse response8 = d_rewriter->postRewrite(n8);
  ASSERT_TRUE(response8.d_node == emptyBag
              && response8.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_remove A (bag.union_max B A)) =
  // (as bag.empty (Bag String))
  Node n9 = d_nodeManager->mkNode(BAG_DIFFERENCE_REMOVE, A, unionMaxBA);
  RewriteResponse response9 = d_rewriter->postRewrite(n9);
  ASSERT_TRUE(response9.d_node == emptyBag
              && response9.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_remove (bag.inter_min A B) A) =
  // (as bag.empty (Bag String))
  Node n10 = d_nodeManager->mkNode(BAG_DIFFERENCE_REMOVE, intersectionAB, A);
  RewriteResponse response10 = d_rewriter->postRewrite(n10);
  ASSERT_TRUE(response10.d_node == emptyBag
              && response10.d_status == REWRITE_AGAIN_FULL);

  // (bag.difference_remove (bag.inter_min B A) A) =
  // (as bag.empty (Bag String))
  Node n11 = d_nodeManager->mkNode(BAG_DIFFERENCE_REMOVE, intersectionBA, A);
  RewriteResponse response11 = d_rewriter->postRewrite(n11);
  ASSERT_TRUE(response11.d_node == emptyBag
              && response11.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, choose)
{
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node c = d_nodeManager->mkConstInt(Rational(3));
  Node bag = d_nodeManager->mkNode(BAG_MAKE, x, c);

  // (bag.choose (bag x c)) = x where c is a constant > 0
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
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node c = d_nodeManager->mkConstInt(Rational(3));
  Node bag = d_nodeManager->mkNode(BAG_MAKE, x, c);
  std::vector<Node> elements = getNStrings(2);
  Node A = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(4)));
  Node B = d_nodeManager->mkNode(
      BAG_MAKE, elements[1], d_nodeManager->mkConstInt(Rational(5)));
  Node unionDisjointAB = d_nodeManager->mkNode(BAG_UNION_DISJOINT, A, B);

  // (bag.card (as bag.empty (Bag String)) = 0
  Node n1 = d_nodeManager->mkNode(BAG_CARD, emptyBag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == zero
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (bag.card (bag x c)) = c where c is a constant > 0
  Node n2 = d_nodeManager->mkNode(BAG_CARD, bag);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  ASSERT_TRUE(response2.d_node == c
              && response2.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, is_singleton)
{
  Node emptybag = d_nodeManager->mkConst(
      EmptyBag(d_nodeManager->mkBagType(d_nodeManager->stringType())));
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node c = d_skolemManager->mkDummySkolem("c", d_nodeManager->integerType());
  Node bag = d_nodeManager->mkNode(BAG_MAKE, x, c);

  // (bag.is_singleton (as bag.empty (Bag String)) = false
  Node n1 = d_nodeManager->mkNode(BAG_IS_SINGLETON, emptybag);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == d_nodeManager->mkConst(false)
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (bag.is_singleton (bag x c) = (c == 1)
  Node n2 = d_nodeManager->mkNode(BAG_IS_SINGLETON, bag);
  RewriteResponse response2 = d_rewriter->postRewrite(n2);
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node equal = c.eqNode(one);
  ASSERT_TRUE(response2.d_node == equal
              && response2.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, from_set)
{
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node singleton = d_nodeManager->mkNode(SET_SINGLETON, x);

  // (bag.from_set (set.singleton (set.singleton_op Int) x)) = (bag x 1)
  Node n = d_nodeManager->mkNode(BAG_FROM_SET, singleton);
  RewriteResponse response = d_rewriter->postRewrite(n);
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node bag = d_nodeManager->mkNode(BAG_MAKE, x, one);
  ASSERT_TRUE(response.d_node == bag
              && response.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, to_set)
{
  Node x = d_skolemManager->mkDummySkolem("x", d_nodeManager->stringType());
  Node bag = d_nodeManager->mkNode(
      BAG_MAKE, x, d_nodeManager->mkConstInt(Rational(5)));

  // (bag.to_set (bag x n)) = (set.singleton (set.singleton_op T) x)
  Node n = d_nodeManager->mkNode(BAG_TO_SET, bag);
  RewriteResponse response = d_rewriter->postRewrite(n);
  Node singleton = d_nodeManager->mkNode(SET_SINGLETON, x);
  ASSERT_TRUE(response.d_node == singleton
              && response.d_status == REWRITE_AGAIN_FULL);
}

TEST_F(TestTheoryWhiteBagsRewriter, map)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  TypeNode bagStringType =
      d_nodeManager->mkBagType(d_nodeManager->stringType());
  Node emptybagString = d_nodeManager->mkConst(EmptyBag(bagStringType));

  Node empty = d_nodeManager->mkConst(String(""));
  Node xString = d_nodeManager->mkBoundVar("x", d_nodeManager->stringType());
  Node bound = d_nodeManager->mkNode(BOUND_VAR_LIST, xString);
  Node lambda = d_nodeManager->mkNode(LAMBDA, bound, empty);

  // (bag.map (lambda ((x U))  t) (as bag.empty (Bag String)) =
  // (as bag.empty (Bag String))
  Node n1 = d_nodeManager->mkNode(BAG_MAP, lambda, emptybagString);
  RewriteResponse response1 = d_rewriter->postRewrite(n1);
  ASSERT_TRUE(response1.d_node == emptybagString
              && response1.d_status == REWRITE_AGAIN_FULL);

  std::vector<Node> elements = getNStrings(2);
  Node a = d_nodeManager->mkConst(String("a"));
  Node b = d_nodeManager->mkConst(String("b"));
  Node A = d_nodeManager->mkNode(
      BAG_MAKE, a, d_nodeManager->mkConstInt(Rational(3)));
  Node B = d_nodeManager->mkNode(
      BAG_MAKE, b, d_nodeManager->mkConstInt(Rational(4)));
  Node unionDisjointAB = d_nodeManager->mkNode(BAG_UNION_DISJOINT, A, B);

  ASSERT_TRUE(unionDisjointAB.isConst());

  // (bag.map
  //   (lambda ((x Int)) "")
  //   (bag.union_disjoint (bag "a" 3) (bag "b" 4))) =
  // (bag "" 7))
  Node n2 = d_nodeManager->mkNode(BAG_MAP, lambda, unionDisjointAB);
  Node rewritten = rr->rewrite(n2);
  Node bag = d_nodeManager->mkNode(
      BAG_MAKE, empty, d_nodeManager->mkConstInt(Rational(7)));
  //  - (bag.map f (bag.union_disjoint K1 K2)) =
  //      (bag.union_disjoint (bag.map f K1) (bag.map f K2))
  Node k1 = d_skolemManager->mkDummySkolem("K1", A.getType());
  Node k2 = d_skolemManager->mkDummySkolem("K2", A.getType());
  Node f = d_skolemManager->mkDummySkolem("f", lambda.getType());
  Node unionDisjointK1K2 = d_nodeManager->mkNode(BAG_UNION_DISJOINT, k1, k2);
  Node n3 = d_nodeManager->mkNode(BAG_MAP, f, unionDisjointK1K2);
  Node rewritten3 = rr->rewrite(n3);
  Node mapK1 = d_nodeManager->mkNode(BAG_MAP, f, k1);
  Node mapK2 = d_nodeManager->mkNode(BAG_MAP, f, k2);
  Node unionDisjointMapK1K2 =
      d_nodeManager->mkNode(BAG_UNION_DISJOINT, mapK1, mapK2);
  ASSERT_TRUE(rewritten3 == unionDisjointMapK1K2);
}

TEST_F(TestTheoryWhiteBagsRewriter, fold)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  TypeNode bagIntegerType =
      d_nodeManager->mkBagType(d_nodeManager->integerType());
  Node emptybag = d_nodeManager->mkConst(EmptyBag(bagIntegerType));
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node ten = d_nodeManager->mkConstInt(Rational(10));
  Node n = d_nodeManager->mkConstInt(Rational(2));
  Node x = d_nodeManager->mkBoundVar("x", d_nodeManager->integerType());
  Node y = d_nodeManager->mkBoundVar("y", d_nodeManager->integerType());
  Node xy = d_nodeManager->mkNode(BOUND_VAR_LIST, x, y);
  Node sum = d_nodeManager->mkNode(ADD, x, y);

  // f(x,y) = 0 for all x, y
  Node f = d_nodeManager->mkNode(LAMBDA, xy, zero);
  Node node1 = d_nodeManager->mkNode(BAG_FOLD, f, one, emptybag);
  RewriteResponse response1 = d_rewriter->postRewrite(node1);
  ASSERT_TRUE(response1.d_node == one
              && response1.d_status == REWRITE_AGAIN_FULL);

  // (bag.fold f t (bag x n)) = (f t ... (f t (f t x))) n times,  where n > 0
  f = d_nodeManager->mkNode(LAMBDA, xy, sum);
  Node xSkolem = d_nodeManager->getSkolemManager()->mkDummySkolem(
      "x", d_nodeManager->integerType());
  Node bag = d_nodeManager->mkNode(BAG_MAKE, xSkolem, n);
  Node node2 = d_nodeManager->mkNode(BAG_FOLD, f, one, bag);
  Node apply_f_once = d_nodeManager->mkNode(APPLY_UF, f, xSkolem, one);
  Node apply_f_twice =
      d_nodeManager->mkNode(APPLY_UF, f, xSkolem, apply_f_once);
  RewriteResponse response2 = d_rewriter->postRewrite(node2);
  ASSERT_TRUE(response2.d_node == apply_f_twice
              && response2.d_status == REWRITE_AGAIN_FULL);

  // (bag.fold (lambda ((x Int)(y Int)) (+ x y)) 1 (bag 10 2)) = 21
  bag = d_nodeManager->mkNode(BAG_MAKE, ten, n);
  Node node3 = d_nodeManager->mkNode(BAG_FOLD, f, one, bag);
  Node result3 = d_nodeManager->mkConstInt(Rational(21));
  Node response3 = rr->rewrite(node3);
  ASSERT_TRUE(response3 == result3);

  // (bag.fold f t (bag.union_disjoint A B)) =
  //       (bag.fold f (bag.fold f t A) B) where A < B to break symmetry

  Node A =
      d_nodeManager->getSkolemManager()->mkDummySkolem("A", bagIntegerType);
  Node B =
      d_nodeManager->getSkolemManager()->mkDummySkolem("B", bagIntegerType);
  Node disjoint = d_nodeManager->mkNode(BAG_UNION_DISJOINT, A, B);
  Node node4 = d_nodeManager->mkNode(BAG_FOLD, f, one, disjoint);
  Node foldA = d_nodeManager->mkNode(BAG_FOLD, f, one, A);
  Node fold = d_nodeManager->mkNode(BAG_FOLD, f, foldA, B);
  RewriteResponse response4 = d_rewriter->postRewrite(node4);
  ASSERT_TRUE(response4.d_node == fold
              && response2.d_status == REWRITE_AGAIN_FULL);
}

}  // namespace test
}  // namespace cvc5::internal
