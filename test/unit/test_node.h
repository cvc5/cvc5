/*********************                                                        */
/*! \file test_expr.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Common header for Node unit tests.
 **/

#ifndef CVC4__TEST__UNIT__TEST_NODE_H
#define CVC4__TEST__UNIT__TEST_NODE_H

#include "expr/node_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "test.h"
#include "test_api.h"

namespace CVC4 {
namespace test {

class TestNodeBlack : public TestInternal
{
 protected:
  void SetUp() override
  {
    d_nodeManager.reset(new NodeManager(nullptr));
    d_scope.reset(new NodeManagerScope(d_nodeManager.get()));
    d_intTypeNode.reset(new TypeNode(d_nodeManager->integerType()));
    d_boolTypeNode.reset(new TypeNode(d_nodeManager->booleanType()));
    d_bvTypeNode.reset(new TypeNode(d_nodeManager->mkBitVectorType(2)));
  }

  std::unique_ptr<NodeManagerScope> d_scope;
  std::unique_ptr<NodeManager> d_nodeManager;
  std::unique_ptr<TypeNode> d_intTypeNode;
  std::unique_ptr<TypeNode> d_boolTypeNode;
  std::unique_ptr<TypeNode> d_bvTypeNode;
};

}  // namespace test
}  // namespace CVC4
#endif
