/*********************                                                        */
/*! \file type_node_white.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of TypeNode
 **
 ** White box testing of TypeNode.
 **/

#include <iostream>
#include <sstream>
#include <string>

#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/node_manager.h"
#include "expr/type_node.h"
#include "smt/smt_engine.h"
#include "test_node.h"

namespace CVC4 {

using namespace kind;
using namespace context;

namespace test {

class TestNodeWhiteTypeNode : public TestNodeWhite
{
 protected:
  void SetUp() override
  {
    TestNodeWhite::SetUp();
    d_smt.reset(new SmtEngine(d_nodeManager.get()));
  }
  std::unique_ptr<SmtEngine> d_smt;
};

TEST_F(TestNodeWhiteTypeNode, sub_types)
{
  TypeNode realType = d_nodeManager->realType();
  TypeNode integerType = d_nodeManager->realType();
  TypeNode booleanType = d_nodeManager->booleanType();
  TypeNode arrayType = d_nodeManager->mkArrayType(realType, integerType);
  TypeNode bvType = d_nodeManager->mkBitVectorType(32);

  Node x = d_nodeManager->mkBoundVar("x", realType);
  Node xPos = d_nodeManager->mkNode(GT, x, d_nodeManager->mkConst(Rational(0)));
  TypeNode funtype = d_nodeManager->mkFunctionType(integerType, booleanType);
  Node lambda = d_nodeManager->mkVar("lambda", funtype);
  std::vector<Node> formals;
  formals.push_back(x);
  d_smt->defineFunction(lambda, formals, xPos);

  ASSERT_FALSE(realType.isComparableTo(booleanType));
  ASSERT_TRUE(realType.isComparableTo(integerType));
  ASSERT_TRUE(realType.isComparableTo(realType));
  ASSERT_FALSE(realType.isComparableTo(arrayType));
  ASSERT_FALSE(realType.isComparableTo(bvType));

  ASSERT_FALSE(booleanType.isComparableTo(integerType));
  ASSERT_FALSE(booleanType.isComparableTo(realType));
  ASSERT_TRUE(booleanType.isComparableTo(booleanType));
  ASSERT_FALSE(booleanType.isComparableTo(arrayType));
  ASSERT_FALSE(booleanType.isComparableTo(bvType));

  ASSERT_TRUE(integerType.isComparableTo(realType));
  ASSERT_TRUE(integerType.isComparableTo(integerType));
  ASSERT_FALSE(integerType.isComparableTo(booleanType));
  ASSERT_FALSE(integerType.isComparableTo(arrayType));
  ASSERT_FALSE(integerType.isComparableTo(bvType));

  ASSERT_FALSE(arrayType.isComparableTo(booleanType));
  ASSERT_FALSE(arrayType.isComparableTo(integerType));
  ASSERT_FALSE(arrayType.isComparableTo(realType));
  ASSERT_TRUE(arrayType.isComparableTo(arrayType));
  ASSERT_FALSE(arrayType.isComparableTo(bvType));

  ASSERT_FALSE(bvType.isComparableTo(booleanType));
  ASSERT_FALSE(bvType.isComparableTo(integerType));
  ASSERT_FALSE(bvType.isComparableTo(realType));
  ASSERT_FALSE(bvType.isComparableTo(arrayType));
  ASSERT_TRUE(bvType.isComparableTo(bvType));

  ASSERT_TRUE(realType.getBaseType() == realType);
  ASSERT_TRUE(integerType.getBaseType() == realType);
  ASSERT_TRUE(booleanType.getBaseType() == booleanType);
  ASSERT_TRUE(arrayType.getBaseType() == arrayType);
  ASSERT_TRUE(bvType.getBaseType() == bvType);
}
}  // namespace test
}  // namespace CVC4
