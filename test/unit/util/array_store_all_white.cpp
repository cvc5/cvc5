/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::ArrayStoreAll.
 */

#include "expr/array_store_all.h"
#include "test_smt.h"
#include "util/rational.h"
#include "util/uninterpreted_sort_value.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace test {

class TestUtilWhiteArrayStoreAll : public TestSmt
{
};

TEST_F(TestUtilWhiteArrayStoreAll, store_all)
{
  TypeNode usort = d_nodeManager->mkSort("U");
  ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                           d_nodeManager->realType()),
                d_nodeManager->mkConstReal(Rational(9, 2)));
  ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->mkSort("U"), usort),
                d_nodeManager->mkConst(UninterpretedSortValue(usort, 0)));
  ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->mkBitVectorType(8),
                                           d_nodeManager->realType()),
                d_nodeManager->mkConstReal(Rational(0)));
  ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->mkBitVectorType(8),
                                           d_nodeManager->integerType()),
                d_nodeManager->mkConstInt(Rational(0)));
}

TEST_F(TestUtilWhiteArrayStoreAll, type_errors)
{
  ASSERT_DEATH(ArrayStoreAll(d_nodeManager->integerType(),
                             d_nodeManager->mkConst(UninterpretedSortValue(
                                 d_nodeManager->mkSort("U"), 0))),
               "can only be created for array types");
  ASSERT_DEATH(ArrayStoreAll(d_nodeManager->integerType(),
                             d_nodeManager->mkConstReal(Rational(9, 2))),
               "can only be created for array types");
  ASSERT_DEATH(
      ArrayStoreAll(d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                               d_nodeManager->mkSort("U")),
                    d_nodeManager->mkConstReal(Rational(9, 2))),
      "does not match constituent type of array type");
  ASSERT_DEATH(ArrayStoreAll(
                   d_nodeManager->mkArrayType(d_nodeManager->mkBitVectorType(8),
                                              d_nodeManager->realType()),
                   d_nodeManager->mkConstInt(Rational(0))),
               "does not match constituent type of array type");
}

TEST_F(TestUtilWhiteArrayStoreAll, const_error)
{
  TypeNode usort = d_nodeManager->mkSort("U");
  ASSERT_DEATH(ArrayStoreAll(d_nodeManager->mkArrayType(
                                 d_nodeManager->mkSort("U"), usort),
                             d_nodeManager->mkVar(usort)),
               "requires a constant expression");
  ASSERT_DEATH(
      ArrayStoreAll(d_nodeManager->integerType(),
                    d_nodeManager->mkVar("x", d_nodeManager->integerType())),
      "array store-all constants can only be created for array types");
  ASSERT_DEATH(ArrayStoreAll(d_nodeManager->integerType(),
                             d_nodeManager->mkNode(
                                 kind::ADD,
                                 d_nodeManager->mkConstInt(Rational(1)),
                                 d_nodeManager->mkConstInt(Rational(0)))),
               "array store-all constants can only be created for array types");
}
}  // namespace test
}  // namespace cvc5::internal
