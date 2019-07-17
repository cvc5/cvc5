/*********************                                                        */
/*! \file node_algorithm_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of utility functions in node_algorithm.{h,cpp}
 **
 ** Black box testing of node_algorithm.{h,cpp}
 **/

#include <cxxtest/TestSuite.h>

#include <string>
#include <vector>

#include "base/output.h"
#include "expr/node_algorithm.h"
#include "expr/node_manager.h"
#include "util/integer.h"
#include "util/rational.h"

using namespace CVC4;
using namespace CVC4::expr;
using namespace CVC4::kind;

class NodeAlgorithmBlack : public CxxTest::TestSuite {

private:
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;
  TypeNode* d_intTypeNode;

 public:
  void setUp() override
  {
    d_nodeManager = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nodeManager);
    d_intTypeNode = new TypeNode(d_nodeManager->integerType());
  }

  void tearDown() override
  {
    delete d_intTypeNode;
    delete d_scope;
    delete d_nodeManager;
  }

  void testGetSymbols1() {
    Node x = d_nodeManager->mkSkolem("x",d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(NOT, x);
    std::unordered_set<Node, NodeHashFunction> syms;
    getSymbols(n, syms);
    TS_ASSERT_EQUALS(syms.size(), 1);
    TS_ASSERT(syms.find(x) != syms.end());
  }

  void testGetSymbols2() {
    Node x = d_nodeManager->mkSkolem("x",d_nodeManager->integerType());
    Node y = d_nodeManager->mkSkolem("y",d_nodeManager->integerType());
    Node left = d_nodeManager->mkNode(EQUAL, x, y);
    Node var = d_nodeManager->mkBoundVar(*d_intTypeNode);
    std::vector<Node> vars;
    vars.push_back(var);
    Node sum = d_nodeManager->mkNode(PLUS, var, var);
    Node qeq = d_nodeManager->mkNode(EQUAL, x, sum);
    Node bvl = d_nodeManager->mkNode(BOUND_VAR_LIST, vars);
    Node right = d_nodeManager->mkNode(EXISTS, bvl, qeq);
    Node res = d_nodeManager->mkNode(AND, left, right);
    std::unordered_set<Node, NodeHashFunction> syms;
    getSymbols(res, syms);
    TS_ASSERT_EQUALS(syms.size(), 2);
    TS_ASSERT(syms.find(x) != syms.end());
    TS_ASSERT(syms.find(y) != syms.end());
    TS_ASSERT(syms.find(var) == syms.end());
  }

};
