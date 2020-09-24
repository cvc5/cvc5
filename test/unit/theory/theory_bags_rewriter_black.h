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
#include "theory/bags/theory_bags_rewriter.h"
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
  }

  void tearDown() override
  {
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
    RewriteResponse response = d_rewriter.postRewrite(emptybag);
    TS_ASSERT(emptybag == response.d_node && response.d_status == REWRITE_DONE);
  }

  void testBagEquality()
  {
    vector<Node> elements = getNStrings(1);
    Node emptyBag1 =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node emptyBag2 =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(d_nm->stringType())));
    Node equal = emptyBag1.eqNode(emptyBag2);

    RewriteResponse response = d_rewriter.preRewrite(equal);
    TS_ASSERT(response.d_node == d_nm->mkConst(true)
              && response.d_status == REWRITE_DONE);
  }

  void testMkBagConstantElement()
  {
    vector<Node> elements = getNStrings(1);
    Node negative =
        d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(-1)));
    Node zero = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(0)));
    Node positive =
        d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(1)));
    RewriteResponse negativeResponse = d_rewriter.postRewrite(negative);
    RewriteResponse zeroResponse = d_rewriter.postRewrite(zero);
    RewriteResponse positiveResponse = d_rewriter.postRewrite(positive);

    // bags with non-positive multiplicity are rewritten as empty bags
    TS_ASSERT(negativeResponse.d_status == REWRITE_AGAIN
              && negativeResponse.d_node.getKind() == EMPTYBAG
              && negativeResponse.d_node.getType() == negative.getType());
    TS_ASSERT(zeroResponse.d_status == REWRITE_AGAIN
              && zeroResponse.d_node.getKind() == EMPTYBAG
              && zeroResponse.d_node.getType() == negative.getType());

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
    RewriteResponse negativeResponse = d_rewriter.postRewrite(negative);
    RewriteResponse zeroResponse = d_rewriter.postRewrite(zero);
    RewriteResponse positiveResponse = d_rewriter.postRewrite(positive);

    // bags with non-positive multiplicity are rewritten as empty bags
    TS_ASSERT(negativeResponse.d_status == REWRITE_AGAIN
              && negativeResponse.d_node.getKind() == EMPTYBAG
              && negativeResponse.d_node.getType() == negative.getType());
    TS_ASSERT(zeroResponse.d_status == REWRITE_AGAIN
              && zeroResponse.d_node.getKind() == EMPTYBAG
              && zeroResponse.d_node.getType() == negative.getType());

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

    std::cout << emptyBag.getType() << std::endl;
    Node emptyCount = d_nm->mkNode(BAG_COUNT, skolem, emptyBag);
    Node bagCount = d_nm->mkNode(BAG_COUNT, skolem, bag);

    RewriteResponse zeroResponse = d_rewriter.postRewrite(emptyCount);
    RewriteResponse nResponse = d_rewriter.postRewrite(bagCount);

    TS_ASSERT(zeroResponse.d_status == REWRITE_AGAIN
              && zeroResponse.d_node.isConst());
    //&& zeroResponse.d_node.getConst<Rational>().isZero());

    // no change for positive
    TS_ASSERT(
        nResponse.d_status == REWRITE_AGAIN && nResponse.d_node.isConst()
        && nResponse.d_node.getConst<Rational>().getNumerator().toUnsignedInt()
               == n);
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
    RewriteResponse response1 = d_rewriter.postRewrite(unionMax1);
    TS_ASSERT(response1.d_node == A && response1.d_status == REWRITE_AGAIN);

    // (union_max emptybag A) = A
    Node unionMax2 = d_nm->mkNode(UNION_MAX, emptyBag, A);
    RewriteResponse response2 = d_rewriter.postRewrite(unionMax2);
    TS_ASSERT(response2.d_node == A && response2.d_status == REWRITE_AGAIN);

    // (union_max A A) = A
    Node unionMax3 = d_nm->mkNode(UNION_MAX, emptyBag, A);
    RewriteResponse response3 = d_rewriter.postRewrite(unionMax3);
    TS_ASSERT(response3.d_node == A && response3.d_status == REWRITE_AGAIN);

    // (union_max A (union_max A B) = (union_max A B)
    Node unionMax4 = d_nm->mkNode(UNION_MAX, A, unionMaxAB);
    RewriteResponse response4 = d_rewriter.postRewrite(unionMax4);
    TS_ASSERT(response4.d_node == unionMaxAB
              && response4.d_status == REWRITE_AGAIN);

    // (union_max A (union_max B A) = (union_max B A)
    Node unionMax5 = d_nm->mkNode(UNION_MAX, A, unionMaxBA);
    RewriteResponse response5 = d_rewriter.postRewrite(unionMax5);
    TS_ASSERT(response5.d_node == unionMaxBA
              && response4.d_status == REWRITE_AGAIN);

    // (union_max (union_max A B) A) = (union_max A B)
    Node unionMax6 = d_nm->mkNode(UNION_MAX, unionMaxAB, A);
    RewriteResponse response6 = d_rewriter.postRewrite(unionMax6);
    TS_ASSERT(response6.d_node == unionMaxAB
              && response6.d_status == REWRITE_AGAIN);

    // (union_max (union_max B A) A) = (union_max B A)
    Node unionMax7 = d_nm->mkNode(UNION_MAX, unionMaxBA, A);
    RewriteResponse response7 = d_rewriter.postRewrite(unionMax7);
    TS_ASSERT(response7.d_node == unionMaxBA
              && response7.d_status == REWRITE_AGAIN);

    // (union_max A (union_disjoint A B) = (union_disjoint A B)
    Node unionMax8 = d_nm->mkNode(UNION_MAX, A, unionDisjointAB);
    RewriteResponse response8 = d_rewriter.postRewrite(unionMax8);
    TS_ASSERT(response8.d_node == unionDisjointAB
              && response8.d_status == REWRITE_AGAIN);

    // (union_max A (union_disjoint B A) = (union_disjoint B A)
    Node unionMax9 = d_nm->mkNode(UNION_MAX, A, unionDisjointBA);
    RewriteResponse response9 = d_rewriter.postRewrite(unionMax9);
    TS_ASSERT(response9.d_node == unionDisjointBA
              && response9.d_status == REWRITE_AGAIN);

    // (union_max (union_disjoint A B) A) = (union_disjoint A B)
    Node unionMax10 = d_nm->mkNode(UNION_MAX, unionDisjointAB, A);
    RewriteResponse response10 = d_rewriter.postRewrite(unionMax10);
    TS_ASSERT(response10.d_node == unionDisjointAB
              && response10.d_status == REWRITE_AGAIN);

    // (union_max (union_disjoint B A) A) = (union_disjoint B A)
    Node unionMax11 = d_nm->mkNode(UNION_MAX, unionDisjointBA, A);
    RewriteResponse response11 = d_rewriter.postRewrite(unionMax11);
    TS_ASSERT(response11.d_node == unionDisjointBA
              && response11.d_status == REWRITE_AGAIN);
  }

 private:
  std::unique_ptr<ExprManager> d_em;
  std::unique_ptr<SmtEngine> d_smt;
  std::unique_ptr<NodeManager> d_nm;
  TheoryBagsRewriter d_rewriter;
}; /* class BagsTypeRuleBlack */
