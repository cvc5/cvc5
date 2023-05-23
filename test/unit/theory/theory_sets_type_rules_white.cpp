/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Mudathir Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
  Sort realSort = d_solver.getRealSort();
  Sort intSort = d_solver.getIntegerSort();
  Term emptyReal = d_solver.mkEmptySet(d_solver.mkSetSort(realSort));
  Term integerOne = d_solver.mkInteger(1);
  Term realOne = d_solver.mkReal(1);
  Term singletonInt = d_solver.mkTerm(cvc5::SET_SINGLETON, {integerOne});
  Term singletonReal = d_solver.mkTerm(cvc5::SET_SINGLETON, {realOne});
  // (union
  //    (singleton (singleton_op Int) 1)
  //    (as emptyset (Set Real)))
  ASSERT_THROW(d_solver.mkTerm(SET_UNION, {singletonInt, emptyReal}),
               CVC5ApiException);
  // (union
  //    (singleton (singleton_op Real) 1)
  //    (as emptyset (Set Real)))
  ASSERT_NO_THROW(d_solver.mkTerm(SET_UNION, {singletonReal, emptyReal}));
}

TEST_F(TestTheoryWhiteSetsTypeRuleInternal, singleton_node)
{
  Node intConstant = d_nodeManager->mkConstReal(Rational(1));
  Node realConstant = d_nodeManager->mkConstReal(Rational(1, 5));
  // (singleton (singleton_op Real) 1)
  ASSERT_NO_THROW(d_nodeManager->mkNode(kind::SET_SINGLETON, intConstant));

  Node n = d_nodeManager->mkNode(kind::SET_SINGLETON, intConstant);
  // the type of (singleton (singleton_op Real) 1) is (Set Real)
  ASSERT_TRUE(n.getType()
              == d_nodeManager->mkSetType(d_nodeManager->realType()));
  // (singleton (singleton_op Real) 1) is a constant in normal form
  ASSERT_TRUE(n.isConst());
}
}  // namespace test
}  // namespace cvc5::internal
