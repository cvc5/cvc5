/*********************                                                        */
/*! \file theory_bags_type_rules_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of bags typing rules
 **/

#include <cxxtest/TestSuite.h>

#include "expr/dtype.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "theory/bags/theory_bags_type_rules.h"
#include "theory/strings/type_enumerator.h"

using namespace CVC4;
using namespace CVC4::smt;
using namespace CVC4::theory;
using namespace CVC4::kind;
using namespace CVC4::theory::bags;
using namespace std;

typedef expr::Attribute<Node, Node> attribute;

class SetEnumeratorWhite : public CxxTest::TestSuite
{
 public:
  void setUp() override
  {
    d_em = new ExprManager();
    d_smt = new SmtEngine(d_em);
    d_nm = NodeManager::fromExprManager(d_em);
    d_scope = new SmtScope(d_smt);
    d_smt->finishInit();
  }

  void tearDown() override
  {
    delete d_scope;
    delete d_smt;
    delete d_em;
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

 private:
  ExprManager* d_em;
  SmtEngine* d_smt;
  NodeManager* d_nm;
  SmtScope* d_scope;
}; /* class SetEnumeratorWhite */
