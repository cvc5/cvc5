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
 * Black box testing of bags typing rules
 */

#include "expr/dtype.h"
#include "test_smt.h"
#include "theory/bags/theory_bags_type_rules.h"
#include "theory/strings/type_enumerator.h"
#include "util/rational.h"

namespace cvc5 {

using namespace theory;
using namespace kind;
using namespace theory::bags;

namespace test {

typedef expr::Attribute<Node, Node> attribute;

class TestTheoryWhiteBagsTypeRule : public TestSmt
{
 protected:
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
};

TEST_F(TestTheoryWhiteBagsTypeRule, count_operator)
{
  std::vector<Node> elements = getNStrings(1);
  Node bag = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                  elements[0],
                                  d_nodeManager->mkConst(Rational(100)));

  Node count = d_nodeManager->mkNode(BAG_COUNT, elements[0], bag);
  Node node = d_nodeManager->mkConst(Rational(10));

  // node of type Int is not compatible with bag of type (Bag String)
  ASSERT_THROW(d_nodeManager->mkNode(BAG_COUNT, node, bag).getType(true),
               TypeCheckingExceptionPrivate);
}

TEST_F(TestTheoryWhiteBagsTypeRule, duplicate_removal_operator)
{
  std::vector<Node> elements = getNStrings(1);
  Node bag = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                  elements[0],
                                  d_nodeManager->mkConst(Rational(10)));
  ASSERT_NO_THROW(d_nodeManager->mkNode(DUPLICATE_REMOVAL, bag));
  ASSERT_EQ(d_nodeManager->mkNode(DUPLICATE_REMOVAL, bag).getType(),
            bag.getType());
}

TEST_F(TestTheoryWhiteBagsTypeRule, mkBag_operator)
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

  // only positive multiplicity are constants
  ASSERT_FALSE(MkBagTypeRule::computeIsConst(d_nodeManager.get(), negative));
  ASSERT_FALSE(MkBagTypeRule::computeIsConst(d_nodeManager.get(), zero));
  ASSERT_TRUE(MkBagTypeRule::computeIsConst(d_nodeManager.get(), positive));
}

TEST_F(TestTheoryWhiteBagsTypeRule, from_set_operator)
{
  std::vector<Node> elements = getNStrings(1);
  Node set =
      d_nodeManager->mkSingleton(d_nodeManager->stringType(), elements[0]);
  ASSERT_NO_THROW(d_nodeManager->mkNode(BAG_FROM_SET, set));
  ASSERT_TRUE(d_nodeManager->mkNode(BAG_FROM_SET, set).getType().isBag());
}

TEST_F(TestTheoryWhiteBagsTypeRule, to_set_operator)
{
  std::vector<Node> elements = getNStrings(1);
  Node bag = d_nodeManager->mkBag(d_nodeManager->stringType(),
                                  elements[0],
                                  d_nodeManager->mkConst(Rational(10)));
  ASSERT_NO_THROW(d_nodeManager->mkNode(BAG_TO_SET, bag));
  ASSERT_TRUE(d_nodeManager->mkNode(BAG_TO_SET, bag).getType().isSet());
}
}  // namespace test
}  // namespace cvc5
