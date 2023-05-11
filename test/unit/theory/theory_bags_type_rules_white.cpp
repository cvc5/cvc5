/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

namespace cvc5::internal {

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
    theory::strings::StringEnumerator enumerator(d_nodeManager->stringType());

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
  Node bag = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(100)));

  Node count = d_nodeManager->mkNode(BAG_COUNT, elements[0], bag);
  Node node = d_nodeManager->mkConstInt(Rational(10));

  // node of type Int is not compatible with bag of type (Bag String)
  ASSERT_THROW(d_nodeManager->mkNode(BAG_COUNT, node, bag).getType(true),
               TypeCheckingExceptionPrivate);
}

TEST_F(TestTheoryWhiteBagsTypeRule, duplicate_removal_operator)
{
  std::vector<Node> elements = getNStrings(1);
  Node bag = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(10)));
  ASSERT_NO_THROW(d_nodeManager->mkNode(BAG_DUPLICATE_REMOVAL, bag));
  ASSERT_EQ(d_nodeManager->mkNode(BAG_DUPLICATE_REMOVAL, bag).getType(),
            bag.getType());
}

TEST_F(TestTheoryWhiteBagsTypeRule, mkBag_operator)
{
  std::vector<Node> elements = getNStrings(1);
  Node negative = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(-1)));
  Node zero = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(0)));
  Node positive = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(1)));

  // only positive multiplicity are constants
  ASSERT_FALSE(BagMakeTypeRule::computeIsConst(d_nodeManager, negative));
  ASSERT_FALSE(BagMakeTypeRule::computeIsConst(d_nodeManager, zero));
  ASSERT_TRUE(BagMakeTypeRule::computeIsConst(d_nodeManager, positive));
}

TEST_F(TestTheoryWhiteBagsTypeRule, from_set_operator)
{
  std::vector<Node> elements = getNStrings(1);
  Node set = d_nodeManager->mkNode(SET_SINGLETON, elements[0]);
  ASSERT_NO_THROW(d_nodeManager->mkNode(BAG_FROM_SET, set));
  ASSERT_TRUE(d_nodeManager->mkNode(BAG_FROM_SET, set).getType().isBag());
}

TEST_F(TestTheoryWhiteBagsTypeRule, to_set_operator)
{
  std::vector<Node> elements = getNStrings(1);
  Node bag = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(10)));
  ASSERT_NO_THROW(d_nodeManager->mkNode(BAG_TO_SET, bag));
  ASSERT_TRUE(d_nodeManager->mkNode(BAG_TO_SET, bag).getType().isSet());
}

TEST_F(TestTheoryWhiteBagsTypeRule, map_operator)
{
  std::vector<Node> elements = getNStrings(1);
  Node bag = d_nodeManager->mkNode(
      BAG_MAKE, elements[0], d_nodeManager->mkConstInt(Rational(10)));
  Node set = d_nodeManager->mkNode(SET_SINGLETON, elements[0]);

  Node x1 = d_nodeManager->mkBoundVar("x", d_nodeManager->stringType());
  Node length = d_nodeManager->mkNode(STRING_LENGTH, x1);
  std::vector<Node> args1;
  args1.push_back(x1);
  Node bound1 = d_nodeManager->mkNode(kind::BOUND_VAR_LIST, args1);
  Node lambda1 = d_nodeManager->mkNode(LAMBDA, bound1, length);

  ASSERT_NO_THROW(d_nodeManager->mkNode(BAG_MAP, lambda1, bag));
  Node mappedBag = d_nodeManager->mkNode(BAG_MAP, lambda1, bag);
  ASSERT_TRUE(mappedBag.getType().isBag());
  ASSERT_EQ(d_nodeManager->integerType(),
            mappedBag.getType().getBagElementType());

  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node x2 = d_nodeManager->mkBoundVar("x", d_nodeManager->integerType());
  std::vector<Node> args2;
  args2.push_back(x2);
  Node bound2 = d_nodeManager->mkNode(kind::BOUND_VAR_LIST, args2);
  Node lambda2 = d_nodeManager->mkNode(LAMBDA, bound2, one);
  ASSERT_THROW(d_nodeManager->mkNode(BAG_MAP, lambda2, bag).getType(true),
               TypeCheckingExceptionPrivate);
  ASSERT_THROW(d_nodeManager->mkNode(BAG_MAP, lambda2, set).getType(true),
               TypeCheckingExceptionPrivate);
}

}  // namespace test
}  // namespace cvc5::internal
