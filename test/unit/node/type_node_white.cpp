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
 * White box testing of TypeNode.
 */

#include <iostream>
#include <sstream>
#include <string>

#include "expr/node_manager.h"
#include "expr/type_node.h"
#include "smt/solver_engine.h"
#include "test_node.h"
#include "util/rational.h"

namespace cvc5::internal {

using namespace kind;
using namespace context;

namespace test {

class TestNodeWhiteTypeNode : public TestNode
{
 protected:
  void SetUp() override
  {
    TestNode::SetUp();
    d_slvEngine.reset(new SolverEngine);
  }
  std::unique_ptr<SolverEngine> d_slvEngine;
};

TEST_F(TestNodeWhiteTypeNode, sub_types)
{
  TypeNode realType = d_nodeManager->realType();
  TypeNode integerType = d_nodeManager->realType();
  TypeNode booleanType = d_nodeManager->booleanType();
  TypeNode arrayType = d_nodeManager->mkArrayType(realType, integerType);
  TypeNode bvType = d_nodeManager->mkBitVectorType(32);

  Node x = d_nodeManager->mkBoundVar("x", realType);
  Node xPos =
      d_nodeManager->mkNode(GT, x, d_nodeManager->mkConstInt(Rational(0)));
  TypeNode funtype = d_nodeManager->mkFunctionType(integerType, booleanType);
  Node lambda = d_nodeManager->mkVar("lambda", funtype);
  std::vector<Node> formals;
  formals.push_back(x);
  d_slvEngine->defineFunction(lambda, formals, xPos);
}
}  // namespace test
}  // namespace cvc5::internal
