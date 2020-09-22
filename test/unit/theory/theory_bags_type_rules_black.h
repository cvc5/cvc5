/*********************                                                        */
/*! \file theory_bags_type_rules_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of bags typing rules
 **/

#include <cxxtest/TestSuite.h>

#include "expr/dtype.h"
#include "smt/smt_engine.h"
#include "theory/bags/theory_bags_type_rules.h"
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

  void testInsertOperator()
  {
    vector<Node> elements = getNStrings(5);
    vector<Node> pairs;
    Node node = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(100)));
    for (int i = 1; i < elements.size(); i++)
    {
      pairs.push_back(elements[i]);
      pairs.push_back(d_nm->mkConst(Rational(i * 2)));
    }
    pairs.push_back(node);

    // (BAG_INSERT "B" 2 "C" 4 "D" 6 "E" 8 (MK_BAG "A" 100))
    Node insert = d_nm->mkNode(BAG_INSERT, pairs);

    // wrong type for the second "E" in
    // (BAG_INSERT "B" 2 "C" 4 "D" 6 "E" "E" (MK_BAG "A" 100))
    pairs[pairs.size() - 2] = pairs[pairs.size() - 3];
    TS_ASSERT_THROWS(d_nm->mkNode(BAG_INSERT, pairs),
                     TypeCheckingExceptionPrivate&);
  }

  void testCountOperator()
  {
    vector<Node> elements = getNStrings(1);
    Node bag = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(100)));

    Node count = d_nm->mkNode(BAG_COUNT, elements[0], bag);
    Node node = d_nm->mkConst(Rational(10));

    // node of type Int is not compatible with bag of type (Bag String)
    TS_ASSERT_THROWS(d_nm->mkNode(BAG_COUNT, node, bag),
                     TypeCheckingExceptionPrivate&);
  }

  void testMkBagOperator()
  {
    vector<Node> elements = getNStrings(1);
    Node negative = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(-1)));
    Node zero = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(0)));
    Node positive = d_nm->mkNode(MK_BAG, elements[0], d_nm->mkConst(Rational(1)));

    // only positive multiplicity are constants
    TS_ASSERT(! MkBagTypeRule::computeIsConst(d_nm.get(), negative));
    TS_ASSERT(! MkBagTypeRule::computeIsConst(d_nm.get(), zero));
    TS_ASSERT(MkBagTypeRule::computeIsConst(d_nm.get(), positive));
  }

 private:
  std::unique_ptr<ExprManager> d_em;
  std::unique_ptr<SmtEngine> d_smt;
  std::unique_ptr<NodeManager> d_nm;
}; /* class BagsTypeRuleBlack */
