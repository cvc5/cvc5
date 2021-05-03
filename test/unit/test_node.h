/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common header for Node unit tests.
 */

#ifndef CVC5__TEST__UNIT__TEST_NODE_H
#define CVC5__TEST__UNIT__TEST_NODE_H

#include "expr/node_manager.h"
#include "expr/skolem_manager.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "test.h"

namespace cvc5 {
namespace test {

class TestNode : public TestInternal
{
 protected:
  void SetUp() override
  {
    d_nodeManager.reset(new NodeManager());
    d_skolemManager = d_nodeManager->getSkolemManager();
    d_scope.reset(new NodeManagerScope(d_nodeManager.get()));
    d_boolTypeNode.reset(new TypeNode(d_nodeManager->booleanType()));
    d_bvTypeNode.reset(new TypeNode(d_nodeManager->mkBitVectorType(2)));
    d_intTypeNode.reset(new TypeNode(d_nodeManager->integerType()));
    d_realTypeNode.reset(new TypeNode(d_nodeManager->realType()));
  }

  std::unique_ptr<NodeManagerScope> d_scope;
  std::unique_ptr<NodeManager> d_nodeManager;
  SkolemManager* d_skolemManager;
  std::unique_ptr<TypeNode> d_boolTypeNode;
  std::unique_ptr<TypeNode> d_bvTypeNode;
  std::unique_ptr<TypeNode> d_intTypeNode;
  std::unique_ptr<TypeNode> d_realTypeNode;
};

}  // namespace test
}  // namespace cvc5
#endif
