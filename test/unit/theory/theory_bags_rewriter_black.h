/*********************                                                        */
/*! \file theory_bags_rewriter_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of bags rewriter
 **/

#include <cxxtest/TestSuite.h>

#include "expr/dtype.h"
#include "smt/smt_engine.h"
#include "theory/bags/bags_rewriter.h"
#include "theory/strings/type_enumerator.h"

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::kind;
using namespace CVC4::theory::bags;
using namespace std;

typedef expr::Attribute<Node, Node> attribute;

class BagsTypeRuleBlack : public CxxTest::TestSuite
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
    for (size_t i = 0; i < n; i++)
    {
      elements[i] = d_nm->mkSkolem("x", d_nm->stringType());
    }
    return elements;
  }

  void testEmptyBagNormalForm()
  {
    Node emptybag = d_nm->mkConst(EmptyBag(d_nm->stringType()));
    // empty bags are in normal form
    TS_ASSERT(emptybag.isConst());
    RewriteResponse response = d_rewriter->postRewrite(emptybag);
    TS_ASSERT(emptybag == response.d_node && response.d_status == REWRITE_DONE);
  }

  void testBagEquality()
  {
    vector<Node> elements = getNStrings(2);
    Node x = elements[0];
    Node y = elements[1];
    Node c = d_nm->mkSkolem("c", d_nm->integerType());
    Node d = d_nm->mkSkolem("d", d_nm->integerType());
    Node bagX = d_nm->mkNode(MK_BAG, x, c);
    Node bagY = d_nm->mkNode(MK_BAG, y, d);
    Node emptyBag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));

    // (= A A) = true where A is a bag
    Node n1 = emptyBag.eqNode(emptyBag);
    RewriteResponse response1 = d_rewriter->preRewrite(n1);
    TS_ASSERT(response1.d_node == d_nm->mkConst(true)
              && response1.d_status == REWRITE_AGAIN_FULL);
  }

  void testMkBagConstantElement()
  {
    vector<Node> elements = getNStrings(1);
    Node negative =
        d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(-1)));
    Node zero = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(0)));
    Node positive =
        d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(1)));
    Node emptybag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    RewriteResponse negativeResponse = d_rewriter->postRewrite(negative);
    RewriteResponse zeroResponse = d_rewriter->postRewrite(zero);
    RewriteResponse positiveResponse = d_rewriter->postRewrite(positive);

    // bags with non-positive multiplicity are rewritten as empty bags
    TS_ASSERT(negativeResponse.d_status == REWRITE_AGAIN_FULL
              && negativeResponse.d_node == emptybag);
    TS_ASSERT(zeroResponse.d_status == REWRITE_AGAIN_FULL
              && zeroResponse.d_node == emptybag);

    // no change for positive
    TS_ASSERT(positiveResponse.d_status == REWRITE_DONE
              && positive == positiveResponse.d_node);
  }

  void testMkBagVariableElement()
  {
    Node skolem = d_nm->mkSkolem("x", d_nm->stringType());
    Node variable = d_nm->mkNode(MK_BAG, skolem, d_nm->mkConst(Rational(-1)));
    Node negative = d_nm->mkNode(MK_BAG, skolem, d_nm->mkConst(Rational(-1)));
    Node zero = d_nm->mkNode(MK_BAG, skolem, d_nm->mkConst(Rational(0)));
    Node positive = d_nm->mkNode(MK_BAG, skolem, d_nm->mkConst(Rational(1)));
    Node emptybag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    RewriteResponse negativeResponse = d_rewriter->postRewrite(negative);
    RewriteResponse zeroResponse = d_rewriter->postRewrite(zero);
    RewriteResponse positiveResponse = d_rewriter->postRewrite(positive);

    // bags with non-positive multiplicity are rewritten as empty bags
    TS_ASSERT(negativeResponse.d_status == REWRITE_AGAIN_FULL
              && negativeResponse.d_node == emptybag);
    TS_ASSERT(zeroResponse.d_status == REWRITE_AGAIN_FULL
              && zeroResponse.d_node == emptybag);

    // no change for positive
    TS_ASSERT(positiveResponse.d_status == REWRITE_DONE
              && positive == positiveResponse.d_node);
  }

  void testBagCount()
  {
    int n = 3;
    Node skolem = d_nm->mkSkolem("x", d_nm->stringType());
    Node emptyBag = d_nm->mkConst(EmptyBag(d_nm->mkBagType(skolem.getType())));
    Node bag = d_nm->mkNode(MK_BAG, skolem, d_nm->mkConst(Rational(n)));

    // (bag.count x emptybag) = 0
    Node n1 = d_nm->mkNode(BAG_COUNT, skolem, emptyBag);
    RewriteResponse response1 = d_rewriter->postRewrite(n1);
    TS_ASSERT(response1.d_status == REWRITE_AGAIN_FULL
              && response1.d_node == d_nm->mkConst(Rational(0)));

    // (bag.count x (mkBag x c) = c where c > 0 is a constant
    Node n2 = d_nm->mkNode(BAG_COUNT, skolem, bag);
    RewriteResponse response2 = d_rewriter->postRewrite(n2);
    TS_ASSERT(response2.d_status == REWRITE_AGAIN_FULL
              && response2.d_node == d_nm->mkConst(Rational(n)));
  }

  void testUnionMax()
  {
    int n = 3;
    vector<Node> elements = getNStrings(2);
    Node emptyBag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node A = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(n)));
    Node B = d_nm->mkNode(MK_BAG, elements[1], d_nm->mkConst(Rational(n + 1)));
    Node unionMaxAB = d_nm->mkNode(UNION_MAX, A, B);
    Node unionMaxBA = d_nm->mkNode(UNION_MAX, B, A);
    Node unionDisjointAB = d_nm->mkNode(UNION_DISJOINT, A, B);
    Node unionDisjointBA = d_nm->mkNode(UNION_DISJOINT, B, A);

    // (union_max A emptybag) = A
    Node unionMax1 = d_nm->mkNode(UNION_MAX, A, emptyBag);
    RewriteResponse response1 = d_rewriter->postRewrite(unionMax1);
    TS_ASSERT(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

    // (union_max emptybag A) = A
    Node unionMax2 = d_nm->mkNode(UNION_MAX, emptyBag, A);
    RewriteResponse response2 = d_rewriter->postRewrite(unionMax2);
    TS_ASSERT(response2.d_node == A
              && response2.d_status == REWRITE_AGAIN_FULL);

    // (union_max A A) = A
    Node unionMax3 = d_nm->mkNode(UNION_MAX, A, A);
    RewriteResponse response3 = d_rewriter->postRewrite(unionMax3);
    TS_ASSERT(response3.d_node == A
              && response3.d_status == REWRITE_AGAIN_FULL);

    // (union_max A (union_max A B)) = (union_max A B)
    Node unionMax4 = d_nm->mkNode(UNION_MAX, A, unionMaxAB);
    RewriteResponse response4 = d_rewriter->postRewrite(unionMax4);
    TS_ASSERT(response4.d_node == unionMaxAB
              && response4.d_status == REWRITE_AGAIN_FULL);

    // (union_max A (union_max B A)) = (union_max B A)
    Node unionMax5 = d_nm->mkNode(UNION_MAX, A, unionMaxBA);
    RewriteResponse response5 = d_rewriter->postRewrite(unionMax5);
    TS_ASSERT(response5.d_node == unionMaxBA
              && response4.d_status == REWRITE_AGAIN_FULL);

    // (union_max (union_max A B) A) = (union_max A B)
    Node unionMax6 = d_nm->mkNode(UNION_MAX, unionMaxAB, A);
    RewriteResponse response6 = d_rewriter->postRewrite(unionMax6);
    TS_ASSERT(response6.d_node == unionMaxAB
              && response6.d_status == REWRITE_AGAIN_FULL);

    // (union_max (union_max B A) A) = (union_max B A)
    Node unionMax7 = d_nm->mkNode(UNION_MAX, unionMaxBA, A);
    RewriteResponse response7 = d_rewriter->postRewrite(unionMax7);
    TS_ASSERT(response7.d_node == unionMaxBA
              && response7.d_status == REWRITE_AGAIN_FULL);

    // (union_max A (union_disjoint A B)) = (union_disjoint A B)
    Node unionMax8 = d_nm->mkNode(UNION_MAX, A, unionDisjointAB);
    RewriteResponse response8 = d_rewriter->postRewrite(unionMax8);
    TS_ASSERT(response8.d_node == unionDisjointAB
              && response8.d_status == REWRITE_AGAIN_FULL);

    // (union_max A (union_disjoint B A)) = (union_disjoint B A)
    Node unionMax9 = d_nm->mkNode(UNION_MAX, A, unionDisjointBA);
    RewriteResponse response9 = d_rewriter->postRewrite(unionMax9);
    TS_ASSERT(response9.d_node == unionDisjointBA
              && response9.d_status == REWRITE_AGAIN_FULL);

    // (union_max (union_disjoint A B) A) = (union_disjoint A B)
    Node unionMax10 = d_nm->mkNode(UNION_MAX, unionDisjointAB, A);
    RewriteResponse response10 = d_rewriter->postRewrite(unionMax10);
    TS_ASSERT(response10.d_node == unionDisjointAB
              && response10.d_status == REWRITE_AGAIN_FULL);

    // (union_max (union_disjoint B A) A) = (union_disjoint B A)
    Node unionMax11 = d_nm->mkNode(UNION_MAX, unionDisjointBA, A);
    RewriteResponse response11 = d_rewriter->postRewrite(unionMax11);
    TS_ASSERT(response11.d_node == unionDisjointBA
              && response11.d_status == REWRITE_AGAIN_FULL);
  }

  void testUnionDisjoint()
  {
    int n = 3;
    vector<Node> elements = getNStrings(2);
    Node emptyBag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node A = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(n)));
    Node B = d_nm->mkNode(MK_BAG, elements[1], d_nm->mkConst(Rational(n + 1)));
    Node unionDisjointAB = d_nm->mkNode(UNION_DISJOINT, A, B);
    Node unionDisjointBA = d_nm->mkNode(UNION_DISJOINT, B, A);
    Node unionMaxAB = d_nm->mkNode(UNION_MAX, A, B);
    Node unionMaxBA = d_nm->mkNode(UNION_MAX, B, A);
    Node intersectionAB = d_nm->mkNode(INTERSECTION_MIN, A, B);
    Node intersectionBA = d_nm->mkNode(INTERSECTION_MIN, B, A);

    // (union_disjoint A emptybag) = A
    Node unionDisjoint1 = d_nm->mkNode(UNION_DISJOINT, A, emptyBag);
    RewriteResponse response1 = d_rewriter->postRewrite(unionDisjoint1);
    TS_ASSERT(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

    // (union_disjoint emptybag A) = A
    Node unionDisjoint2 = d_nm->mkNode(UNION_DISJOINT, emptyBag, A);
    RewriteResponse response2 = d_rewriter->postRewrite(unionDisjoint2);
    TS_ASSERT(response2.d_node == A
              && response2.d_status == REWRITE_AGAIN_FULL);

    // (union_disjoint (union_max A B) (intersection_min B A)) =
    //          (union_disjoint A B) // sum(a,b) = max(a,b) + min(a,b)
    Node unionDisjoint3 =
        d_nm->mkNode(UNION_DISJOINT, unionMaxAB, intersectionBA);
    RewriteResponse response3 = d_rewriter->postRewrite(unionDisjoint3);
    TS_ASSERT(response3.d_node == unionDisjointAB
              && response3.d_status == REWRITE_AGAIN_FULL);

    // (union_disjoint (intersection_min B A)) (union_max A B) =
    //          (union_disjoint B A) // sum(a,b) = max(a,b) + min(a,b)
    Node unionDisjoint4 =
        d_nm->mkNode(UNION_DISJOINT, unionMaxBA, intersectionBA);
    RewriteResponse response4 = d_rewriter->postRewrite(unionDisjoint4);
    TS_ASSERT(response4.d_node == unionDisjointBA
              && response4.d_status == REWRITE_AGAIN_FULL);
  }

  void testIntersectionMin()
  {
    int n = 3;
    vector<Node> elements = getNStrings(2);
    Node emptyBag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node A = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(n)));
    Node B = d_nm->mkNode(MK_BAG, elements[1], d_nm->mkConst(Rational(n + 1)));
    Node unionMaxAB = d_nm->mkNode(UNION_MAX, A, B);
    Node unionMaxBA = d_nm->mkNode(UNION_MAX, B, A);
    Node unionDisjointAB = d_nm->mkNode(UNION_DISJOINT, A, B);
    Node unionDisjointBA = d_nm->mkNode(UNION_DISJOINT, B, A);

    // (intersection_min A emptybag) = emptyBag
    Node n1 = d_nm->mkNode(INTERSECTION_MIN, A, emptyBag);
    RewriteResponse response1 = d_rewriter->postRewrite(n1);
    TS_ASSERT(response1.d_node == emptyBag
              && response1.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min emptybag A) = emptyBag
    Node n2 = d_nm->mkNode(INTERSECTION_MIN, emptyBag, A);
    RewriteResponse response2 = d_rewriter->postRewrite(n2);
    TS_ASSERT(response2.d_node == emptyBag
              && response2.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min A A) = A
    Node n3 = d_nm->mkNode(INTERSECTION_MIN, A, A);
    RewriteResponse response3 = d_rewriter->postRewrite(n3);
    TS_ASSERT(response3.d_node == A
              && response3.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min A (union_max A B) = A
    Node n4 = d_nm->mkNode(INTERSECTION_MIN, A, unionMaxAB);
    RewriteResponse response4 = d_rewriter->postRewrite(n4);
    TS_ASSERT(response4.d_node == A
              && response4.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min A (union_max B A) = A
    Node n5 = d_nm->mkNode(INTERSECTION_MIN, A, unionMaxBA);
    RewriteResponse response5 = d_rewriter->postRewrite(n5);
    TS_ASSERT(response5.d_node == A
              && response4.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min (union_max A B) A) = A
    Node n6 = d_nm->mkNode(INTERSECTION_MIN, unionMaxAB, A);
    RewriteResponse response6 = d_rewriter->postRewrite(n6);
    TS_ASSERT(response6.d_node == A
              && response6.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min (union_max B A) A) = A
    Node n7 = d_nm->mkNode(INTERSECTION_MIN, unionMaxBA, A);
    RewriteResponse response7 = d_rewriter->postRewrite(n7);
    TS_ASSERT(response7.d_node == A
              && response7.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min A (union_disjoint A B) = A
    Node n8 = d_nm->mkNode(INTERSECTION_MIN, A, unionDisjointAB);
    RewriteResponse response8 = d_rewriter->postRewrite(n8);
    TS_ASSERT(response8.d_node == A
              && response8.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min A (union_disjoint B A) = A
    Node n9 = d_nm->mkNode(INTERSECTION_MIN, A, unionDisjointBA);
    RewriteResponse response9 = d_rewriter->postRewrite(n9);
    TS_ASSERT(response9.d_node == A
              && response9.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min (union_disjoint A B) A) = A
    Node n10 = d_nm->mkNode(INTERSECTION_MIN, unionDisjointAB, A);
    RewriteResponse response10 = d_rewriter->postRewrite(n10);
    TS_ASSERT(response10.d_node == A
              && response10.d_status == REWRITE_AGAIN_FULL);

    // (intersection_min (union_disjoint B A) A) = A
    Node n11 = d_nm->mkNode(INTERSECTION_MIN, unionDisjointBA, A);
    RewriteResponse response11 = d_rewriter->postRewrite(n11);
    TS_ASSERT(response11.d_node == A
              && response11.d_status == REWRITE_AGAIN_FULL);
  }

  void testDifferenceSubtract()
  {
    int n = 3;
    vector<Node> elements = getNStrings(2);
    Node emptyBag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node A = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(n)));
    Node B = d_nm->mkNode(MK_BAG, elements[1], d_nm->mkConst(Rational(n + 1)));
    Node unionMaxAB = d_nm->mkNode(UNION_MAX, A, B);
    Node unionMaxBA = d_nm->mkNode(UNION_MAX, B, A);
    Node unionDisjointAB = d_nm->mkNode(UNION_DISJOINT, A, B);
    Node unionDisjointBA = d_nm->mkNode(UNION_DISJOINT, B, A);
    Node intersectionAB = d_nm->mkNode(INTERSECTION_MIN, A, B);
    Node intersectionBA = d_nm->mkNode(INTERSECTION_MIN, B, A);

    // (difference_subtract A emptybag) = A
    Node n1 = d_nm->mkNode(DIFFERENCE_SUBTRACT, A, emptyBag);
    RewriteResponse response1 = d_rewriter->postRewrite(n1);
    TS_ASSERT(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract emptybag A) = emptyBag
    Node n2 = d_nm->mkNode(DIFFERENCE_SUBTRACT, emptyBag, A);
    RewriteResponse response2 = d_rewriter->postRewrite(n2);
    TS_ASSERT(response2.d_node == emptyBag
              && response2.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract A A) = emptybag
    Node n3 = d_nm->mkNode(DIFFERENCE_SUBTRACT, A, A);
    RewriteResponse response3 = d_rewriter->postRewrite(n3);
    TS_ASSERT(response3.d_node == emptyBag
              && response3.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract (union_disjoint A B) A) = B
    Node n4 = d_nm->mkNode(DIFFERENCE_SUBTRACT, unionDisjointAB, A);
    RewriteResponse response4 = d_rewriter->postRewrite(n4);
    TS_ASSERT(response4.d_node == B
              && response4.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract (union_disjoint B A) A) = B
    Node n5 = d_nm->mkNode(DIFFERENCE_SUBTRACT, unionDisjointBA, A);
    RewriteResponse response5 = d_rewriter->postRewrite(n5);
    TS_ASSERT(response5.d_node == B
              && response4.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract A (union_disjoint A B)) = emptybag
    Node n6 = d_nm->mkNode(DIFFERENCE_SUBTRACT, A, unionDisjointAB);
    RewriteResponse response6 = d_rewriter->postRewrite(n6);
    TS_ASSERT(response6.d_node == emptyBag
              && response6.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract A (union_disjoint B A)) = emptybag
    Node n7 = d_nm->mkNode(DIFFERENCE_SUBTRACT, A, unionDisjointBA);
    RewriteResponse response7 = d_rewriter->postRewrite(n7);
    TS_ASSERT(response7.d_node == emptyBag
              && response7.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract A (union_max A B)) = emptybag
    Node n8 = d_nm->mkNode(DIFFERENCE_SUBTRACT, A, unionMaxAB);
    RewriteResponse response8 = d_rewriter->postRewrite(n8);
    TS_ASSERT(response8.d_node == emptyBag
              && response8.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract A (union_max B A)) = emptybag
    Node n9 = d_nm->mkNode(DIFFERENCE_SUBTRACT, A, unionMaxBA);
    RewriteResponse response9 = d_rewriter->postRewrite(n9);
    TS_ASSERT(response9.d_node == emptyBag
              && response9.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract (intersection_min A B) A) = emptybag
    Node n10 = d_nm->mkNode(DIFFERENCE_SUBTRACT, intersectionAB, A);
    RewriteResponse response10 = d_rewriter->postRewrite(n10);
    TS_ASSERT(response10.d_node == emptyBag
              && response10.d_status == REWRITE_AGAIN_FULL);

    // (difference_subtract (intersection_min B A) A) = emptybag
    Node n11 = d_nm->mkNode(DIFFERENCE_SUBTRACT, intersectionBA, A);
    RewriteResponse response11 = d_rewriter->postRewrite(n11);
    TS_ASSERT(response11.d_node == emptyBag
              && response11.d_status == REWRITE_AGAIN_FULL);
  }

  void testDifferenceRemove()
  {
    int n = 3;
    vector<Node> elements = getNStrings(2);
    Node emptyBag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node A = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(n)));
    Node B = d_nm->mkNode(MK_BAG, elements[1], d_nm->mkConst(Rational(n + 1)));
    Node unionMaxAB = d_nm->mkNode(UNION_MAX, A, B);
    Node unionMaxBA = d_nm->mkNode(UNION_MAX, B, A);
    Node unionDisjointAB = d_nm->mkNode(UNION_DISJOINT, A, B);
    Node unionDisjointBA = d_nm->mkNode(UNION_DISJOINT, B, A);
    Node intersectionAB = d_nm->mkNode(INTERSECTION_MIN, A, B);
    Node intersectionBA = d_nm->mkNode(INTERSECTION_MIN, B, A);

    // (difference_remove A emptybag) = A
    Node n1 = d_nm->mkNode(DIFFERENCE_REMOVE, A, emptyBag);
    RewriteResponse response1 = d_rewriter->postRewrite(n1);
    TS_ASSERT(response1.d_node == A
              && response1.d_status == REWRITE_AGAIN_FULL);

    // (difference_remove emptybag A) = emptyBag
    Node n2 = d_nm->mkNode(DIFFERENCE_REMOVE, emptyBag, A);
    RewriteResponse response2 = d_rewriter->postRewrite(n2);
    TS_ASSERT(response2.d_node == emptyBag
              && response2.d_status == REWRITE_AGAIN_FULL);

    // (difference_remove A A) = emptybag
    Node n3 = d_nm->mkNode(DIFFERENCE_REMOVE, A, A);
    RewriteResponse response3 = d_rewriter->postRewrite(n3);
    TS_ASSERT(response3.d_node == emptyBag
              && response3.d_status == REWRITE_AGAIN_FULL);

    // (difference_remove A (union_disjoint A B)) = emptybag
    Node n6 = d_nm->mkNode(DIFFERENCE_REMOVE, A, unionDisjointAB);
    RewriteResponse response6 = d_rewriter->postRewrite(n6);
    TS_ASSERT(response6.d_node == emptyBag
              && response6.d_status == REWRITE_AGAIN_FULL);

    // (difference_remove A (union_disjoint B A)) = emptybag
    Node n7 = d_nm->mkNode(DIFFERENCE_REMOVE, A, unionDisjointBA);
    RewriteResponse response7 = d_rewriter->postRewrite(n7);
    TS_ASSERT(response7.d_node == emptyBag
              && response7.d_status == REWRITE_AGAIN_FULL);

    // (difference_remove A (union_max A B)) = emptybag
    Node n8 = d_nm->mkNode(DIFFERENCE_REMOVE, A, unionMaxAB);
    RewriteResponse response8 = d_rewriter->postRewrite(n8);
    TS_ASSERT(response8.d_node == emptyBag
              && response8.d_status == REWRITE_AGAIN_FULL);

    // (difference_remove A (union_max B A)) = emptybag
    Node n9 = d_nm->mkNode(DIFFERENCE_REMOVE, A, unionMaxBA);
    RewriteResponse response9 = d_rewriter->postRewrite(n9);
    TS_ASSERT(response9.d_node == emptyBag
              && response9.d_status == REWRITE_AGAIN_FULL);

    // (difference_remove (intersection_min A B) A) = emptybag
    Node n10 = d_nm->mkNode(DIFFERENCE_REMOVE, intersectionAB, A);
    RewriteResponse response10 = d_rewriter->postRewrite(n10);
    TS_ASSERT(response10.d_node == emptyBag
              && response10.d_status == REWRITE_AGAIN_FULL);

    // (difference_remove (intersection_min B A) A) = emptybag
    Node n11 = d_nm->mkNode(DIFFERENCE_REMOVE, intersectionBA, A);
    RewriteResponse response11 = d_rewriter->postRewrite(n11);
    TS_ASSERT(response11.d_node == emptyBag
              && response11.d_status == REWRITE_AGAIN_FULL);
  }

  void testChoose()
  {
    Node x = d_nm->mkSkolem("x", d_nm->stringType());
    Node c = d_nm->mkConst(Rational(3));
    Node bag = d_nm->mkNode(MK_BAG, x, c);

    // (bag.choose (mkBag x c)) = x where c is a constant > 0
    Node n1 = d_nm->mkNode(BAG_CHOOSE, bag);
    RewriteResponse response1 = d_rewriter->postRewrite(n1);
    TS_ASSERT(response1.d_node == x
              && response1.d_status == REWRITE_AGAIN_FULL);
  }

  void testBagCard()
  {
    Node x = d_nm->mkSkolem("x", d_nm->stringType());
    Node emptyBag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node zero = d_nm->mkConst(Rational(0));
    Node c = d_nm->mkConst(Rational(3));
    Node bag = d_nm->mkNode(MK_BAG, x, c);
    vector<Node> elements = getNStrings(2);
    Node A = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(4)));
    Node B = d_nm->mkNode(MK_BAG, elements[1], d_nm->mkConst(Rational(5)));
    Node unionDisjointAB = d_nm->mkNode(UNION_DISJOINT, A, B);

    // TODO(projects#223): enable this test after implementing bags normal form
    //    // (bag.card emptybag) = 0
    //    Node n1 = d_nm->mkNode(BAG_CARD, emptyBag);
    //    RewriteResponse response1 = d_rewriter->postRewrite(n1);
    //    TS_ASSERT(response1.d_node == zero && response1.d_status ==
    //    REWRITE_AGAIN_FULL);

    // (bag.card (mkBag x c)) = c where c is a constant > 0
    Node n2 = d_nm->mkNode(BAG_CARD, bag);
    RewriteResponse response2 = d_rewriter->postRewrite(n2);
    TS_ASSERT(response2.d_node == c
              && response2.d_status == REWRITE_AGAIN_FULL);

    // (bag.card (union-disjoint A B)) = (+ (bag.card A) (bag.card B))
    Node n3 = d_nm->mkNode(BAG_CARD, unionDisjointAB);
    Node cardA = d_nm->mkNode(BAG_CARD, A);
    Node cardB = d_nm->mkNode(BAG_CARD, B);
    Node plus = d_nm->mkNode(PLUS, cardA, cardB);
    RewriteResponse response3 = d_rewriter->postRewrite(n3);
    TS_ASSERT(response3.d_node == plus
              && response3.d_status == REWRITE_AGAIN_FULL);
  }

  void testIsSingleton()
  {
    Node emptybag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node x = d_nm->mkSkolem("x", d_nm->stringType());
    Node c = d_nm->mkSkolem("c", d_nm->integerType());
    Node bag = d_nm->mkNode(MK_BAG, x, c);

    // TODO(projects#223): complete this function
    // (bag.is_singleton emptybag) = false
    //    Node n1 = d_nm->mkNode(BAG_IS_SINGLETON, emptybag);
    //    RewriteResponse response1 = d_rewriter->postRewrite(n1);
    //    TS_ASSERT(response1.d_node == d_nm->mkConst(false)
    //              && response1.d_status == REWRITE_AGAIN_FULL);

    // (bag.is_singleton (mkBag x c) = (c == 1)
    Node n2 = d_nm->mkNode(BAG_IS_SINGLETON, bag);
    RewriteResponse response2 = d_rewriter->postRewrite(n2);
    Node one = d_nm->mkConst(Rational(1));
    Node equal = c.eqNode(one);
    TS_ASSERT(response2.d_node == equal
              && response2.d_status == REWRITE_AGAIN_FULL);
  }

 private:
  std::unique_ptr<ExprManager> d_em;
  std::unique_ptr<SmtEngine> d_smt;
  std::unique_ptr<NodeManager> d_nm;

  std::unique_ptr<BagsRewriter> d_rewriter;
}; /* class BagsTypeRuleBlack */
