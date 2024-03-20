/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * White box testing of sets typing rules
 */

#include "expr/dtype.h"
#include "test_api.h"
#include "test_node.h"
#include "util/rational.h"

using namespace cvc5;

namespace cvc5::internal {
namespace test {

class TestTheoryWhiteSetsTypeRuleApi : public TestApi
{
};
class TestTheoryWhiteSetsTypeRuleInternal : public TestNode
{
};

TEST_F(TestTheoryWhiteSetsTypeRuleApi, singleton_term)
{
  Sort realSort = d_tm.getRealSort();
  Sort intSort = d_tm.getIntegerSort();
  Term emptyReal = d_tm.mkEmptySet(d_tm.mkSetSort(realSort));
  Term integerOne = d_tm.mkInteger(1);
  Term realOne = d_tm.mkReal(1);
  Term singletonInt = d_tm.mkTerm(cvc5::Kind::SET_SINGLETON, {integerOne});
  Term singletonReal = d_tm.mkTerm(cvc5::Kind::SET_SINGLETON, {realOne});
  // (union
  //    (singleton (singleton_op Int) 1)
  //    (as emptyset (Set Real)))
  ASSERT_THROW(d_tm.mkTerm(cvc5::Kind::SET_UNION, {singletonInt, emptyReal}),
               CVC5ApiException);
  // (union
  //    (singleton (singleton_op Real) 1)
  //    (as emptyset (Set Real)))
  ASSERT_NO_THROW(
      d_tm.mkTerm(cvc5::Kind::SET_UNION, {singletonReal, emptyReal}));
}

TEST_F(TestTheoryWhiteSetsTypeRuleInternal, singleton_node)
{
  Node intConstant = d_nodeManager->mkConstReal(Rational(1));
  Node realConstant = d_nodeManager->mkConstReal(Rational(1, 5));
  // (singleton (singleton_op Real) 1)
  ASSERT_NO_THROW(d_nodeManager->mkNode(Kind::SET_SINGLETON, intConstant));

  Node n = d_nodeManager->mkNode(Kind::SET_SINGLETON, intConstant);
  // the type of (singleton (singleton_op Real) 1) is (Set Real)
  ASSERT_TRUE(n.getType()
              == d_nodeManager->mkSetType(d_nodeManager->realType()));
  // (singleton (singleton_op Real) 1) is a constant in normal form
  ASSERT_TRUE(n.isConst());
}
}  // namespace test
}  // namespace cvc5::internal
