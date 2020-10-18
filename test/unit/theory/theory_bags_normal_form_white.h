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

  void testMkBagVariableElement() {}

  void testBagCount() {}

  void testUnionMax() {}

  void testUnionDisjoint() {}

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
