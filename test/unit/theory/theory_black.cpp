/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::theory.
 */

#include <sstream>
#include <vector>

#include "expr/array_store_all.h"
#include "expr/node.h"
#include "expr/node_builder.h"
#include "expr/node_value.h"
#include "test_smt.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace kind;
using namespace context;
using namespace theory;

namespace test {

class TestTheoryBlack : public TestSmt
{
};

TEST_F(TestTheoryBlack, array_const)
{
  Rewriter* rr = d_slvEngine->getEnv().getRewriter();
  TypeNode arrType = d_nodeManager->mkArrayType(d_nodeManager->integerType(),
                                                d_nodeManager->integerType());
  Node zero = d_nodeManager->mkConstInt(Rational(0));
  Node one = d_nodeManager->mkConstInt(Rational(1));
  Node storeAll = d_nodeManager->mkConst(ArrayStoreAll(arrType, zero));
  ASSERT_TRUE(storeAll.isConst());

  Node arr = d_nodeManager->mkNode(STORE, storeAll, zero, zero);
  ASSERT_FALSE(arr.isConst());
  arr = rr->rewrite(arr);
  ASSERT_TRUE(arr.isConst());
  arr = d_nodeManager->mkNode(STORE, storeAll, zero, one);
  ASSERT_TRUE(arr.isConst());
  Node arr2 = d_nodeManager->mkNode(STORE, arr, one, zero);
  arr2 = rr->rewrite(arr2);
  ASSERT_TRUE(arr2.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, one, one);
  arr2 = rr->rewrite(arr2);
  ASSERT_TRUE(arr2.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, zero, one);
  arr2 = rr->rewrite(arr2);
  ASSERT_TRUE(arr2.isConst());

  arrType = d_nodeManager->mkArrayType(d_nodeManager->mkBitVectorType(1),
                                       d_nodeManager->mkBitVectorType(1));
  zero = d_nodeManager->mkConst(BitVector(1, 0u));
  one = d_nodeManager->mkConst(BitVector(1, 1u));
  storeAll = d_nodeManager->mkConst(ArrayStoreAll(arrType, zero));
  ASSERT_TRUE(storeAll.isConst());

  arr = d_nodeManager->mkNode(STORE, storeAll, zero, zero);
  ASSERT_FALSE(arr.isConst());
  arr = rr->rewrite(arr);
  ASSERT_TRUE(arr.isConst());
  arr = d_nodeManager->mkNode(STORE, storeAll, zero, one);
  arr = rr->rewrite(arr);
  ASSERT_TRUE(arr.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, one, zero);
  ASSERT_FALSE(arr2.isConst());
  arr2 = rr->rewrite(arr2);
  ASSERT_TRUE(arr2.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, one, one);
  ASSERT_FALSE(arr2.isConst());
  arr2 = rr->rewrite(arr2);
  ASSERT_TRUE(arr2.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, zero, one);
  ASSERT_FALSE(arr2.isConst());
  arr2 = rr->rewrite(arr2);
  ASSERT_TRUE(arr2.isConst());

  arrType = d_nodeManager->mkArrayType(d_nodeManager->mkBitVectorType(2),
                                       d_nodeManager->mkBitVectorType(2));
  zero = d_nodeManager->mkConst(BitVector(2, 0u));
  one = d_nodeManager->mkConst(BitVector(2, 1u));
  Node two = d_nodeManager->mkConst(BitVector(2, 2u));
  Node three = d_nodeManager->mkConst(BitVector(2, 3u));
  storeAll = d_nodeManager->mkConst(ArrayStoreAll(arrType, one));
  ASSERT_TRUE(storeAll.isConst());

  arr = d_nodeManager->mkNode(STORE, storeAll, zero, zero);
  ASSERT_TRUE(arr.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, one, zero);
  ASSERT_FALSE(arr2.isConst());
  arr2 = rr->rewrite(arr2);
  ASSERT_TRUE(arr2.isConst());

  arr = d_nodeManager->mkNode(STORE, storeAll, one, three);
  ASSERT_TRUE(arr.isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr, one, one);
  ASSERT_FALSE(arr2.isConst());
  arr2 = rr->rewrite(arr2);
  ASSERT_TRUE(arr2 == storeAll);

  arr2 = d_nodeManager->mkNode(STORE, arr, zero, zero);
  ASSERT_FALSE(arr2.isConst());
  ASSERT_TRUE(rr->rewrite(arr2).isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr2, two, two);
  ASSERT_FALSE(arr2.isConst());
  ASSERT_TRUE(rr->rewrite(arr2).isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr2, three, one);
  ASSERT_FALSE(arr2.isConst());
  ASSERT_TRUE(rr->rewrite(arr2).isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr2, three, three);
  ASSERT_FALSE(arr2.isConst());
  ASSERT_TRUE(rr->rewrite(arr2).isConst());
  arr2 = d_nodeManager->mkNode(STORE, arr2, two, zero);
  ASSERT_FALSE(arr2.isConst());
  arr2 = rr->rewrite(arr2);
  ASSERT_TRUE(arr2.isConst());
}
}  // namespace test
}  // namespace cvc5::internal
