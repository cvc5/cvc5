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
    vector<Node> elements = getNStrings(1);
    Node emptyBag =
        d_nm->mkConst(EmptyBag(d_nm->mkBagType(elements[0].getType())));
    Node bag = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(n)));

    std::cout << emptyBag.getType() << std::endl;
    Node emptyCount = d_nm->mkNode(BAG_COUNT, elements[0], emptyBag);
    Node bagCount = d_nm->mkNode(BAG_COUNT, elements[0], bag);

    RewriteResponse zeroResponse = d_rewriter.postRewrite(emptyCount);
    RewriteResponse nResponse = d_rewriter.postRewrite(bagCount);

    TS_ASSERT(zeroResponse.d_status == REWRITE_AGAIN
              && zeroResponse.d_node.isConst());
              //&& zeroResponse.d_node.getConst<Rational>().isZero());

    // no change for positive
    TS_ASSERT(nResponse.d_status == REWRITE_AGAIN
              && nResponse.d_node.isConst()
              && nResponse.d_node.getConst<Rational>()
                         .getNumerator().toUnsignedInt() == n);
  }

 private:
  std::unique_ptr<ExprManager> d_em;
  std::unique_ptr<SmtEngine> d_smt;
  std::unique_ptr<NodeManager> d_nm;
  TheoryBagsRewriter d_rewriter;
}; /* class BagsTypeRuleBlack */
