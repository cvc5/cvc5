/*********************                                                        */
/*! \file node_algorithm_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

class NodeAlgorithmBlack : public CxxTest::TestSuite
{
 private:
  NodeManager* d_nodeManager;
  NodeManagerScope* d_scope;
  TypeNode* d_intTypeNode;
  TypeNode* d_boolTypeNode;

 public:
  void setUp() override
  {
    d_nodeManager = new NodeManager(NULL);
    d_scope = new NodeManagerScope(d_nodeManager);
    d_intTypeNode = new TypeNode(d_nodeManager->integerType());
    d_boolTypeNode = new TypeNode(d_nodeManager->booleanType());
  }

  void tearDown() override
  {
    delete d_intTypeNode;
    delete d_boolTypeNode;
    delete d_scope;
    delete d_nodeManager;
  }

  // The only symbol in ~x (x is a boolean varible) should be x
  void testGetSymbols1()
  {
    Node x = d_nodeManager->mkSkolem("x", d_nodeManager->booleanType());
    Node n = d_nodeManager->mkNode(NOT, x);
    std::unordered_set<Node, NodeHashFunction> syms;
    getSymbols(n, syms);
    TS_ASSERT_EQUALS(syms.size(), 1);
    TS_ASSERT(syms.find(x) != syms.end());
  }

  // the only symbols in x=y ^ (exists var. var+var = x) are x and y, because
  // "var" is bound.
  void testGetSymbols2()
  {
    // left conjunct
    Node x = d_nodeManager->mkSkolem("x", d_nodeManager->integerType());
    Node y = d_nodeManager->mkSkolem("y", d_nodeManager->integerType());
    Node left = d_nodeManager->mkNode(EQUAL, x, y);

    // right conjunct
    Node var = d_nodeManager->mkBoundVar(*d_intTypeNode);
    std::vector<Node> vars;
    vars.push_back(var);
    Node sum = d_nodeManager->mkNode(PLUS, var, var);
    Node qeq = d_nodeManager->mkNode(EQUAL, x, sum);
    Node bvl = d_nodeManager->mkNode(BOUND_VAR_LIST, vars);
    Node right = d_nodeManager->mkNode(EXISTS, bvl, qeq);

    // conjunction
    Node res = d_nodeManager->mkNode(AND, left, right);

    // symbols
    std::unordered_set<Node, NodeHashFunction> syms;
    getSymbols(res, syms);

    // assertions
    TS_ASSERT_EQUALS(syms.size(), 2);
    TS_ASSERT(syms.find(x) != syms.end());
    TS_ASSERT(syms.find(y) != syms.end());
    TS_ASSERT(syms.find(var) == syms.end());
  }

  void testGetOperatorsMap()
  {
    // map to store result
    std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> > result =
        std::map<TypeNode, std::unordered_set<Node, NodeHashFunction> >();

    // create test formula
    Node x = d_nodeManager->mkSkolem("x", d_nodeManager->integerType());
    Node plus = d_nodeManager->mkNode(PLUS, x, x);
    Node mul = d_nodeManager->mkNode(MULT, x, x);
    Node eq = d_nodeManager->mkNode(EQUAL, plus, mul);

    // call function
    expr::getOperatorsMap(eq, result);

    // Verify result
    // We should have only integer and boolean as types
    TS_ASSERT(result.size() == 2);
    TS_ASSERT(result.find(*d_intTypeNode) != result.end());
    TS_ASSERT(result.find(*d_boolTypeNode) != result.end());

    // in integers, we should only have plus and mult as operators
    TS_ASSERT(result[*d_intTypeNode].size() == 2);
    TS_ASSERT(result[*d_intTypeNode].find(d_nodeManager->operatorOf(PLUS))
              != result[*d_intTypeNode].end());
    TS_ASSERT(result[*d_intTypeNode].find(d_nodeManager->operatorOf(MULT))
              != result[*d_intTypeNode].end());

    // in booleans, we should only have "=" as an operator.
    TS_ASSERT(result[*d_boolTypeNode].size() == 1);
    TS_ASSERT(result[*d_boolTypeNode].find(d_nodeManager->operatorOf(EQUAL))
              != result[*d_boolTypeNode].end());
  }

  void testMatch()
  {
    TypeNode integer = d_nodeManager->integerType();

    Node one = d_nodeManager->mkConst(Rational(1));
    Node two = d_nodeManager->mkConst(Rational(2));

    Node x = d_nodeManager->mkBoundVar(integer);
    Node a = d_nodeManager->mkSkolem("a", integer);

    Node n1 = d_nodeManager->mkNode(MULT, two, x);
    std::unordered_map<Node, Node, NodeHashFunction> subs;

    // check reflexivity
    TS_ASSERT(match(n1, n1, subs));
    TS_ASSERT_EQUALS(subs.size(), 0);

    Node n2 = d_nodeManager->mkNode(MULT, two, a);
    subs.clear();

    // check instance
    TS_ASSERT(match(n1, n2, subs));
    TS_ASSERT_EQUALS(subs.size(), 1);
    TS_ASSERT_EQUALS(subs[x], a);

    // should return false for flipped arguments (match is not symmetric)
    TS_ASSERT(!match(n2, n1, subs));

    n2 = d_nodeManager->mkNode(MULT, one, a);

    // should return false since n2 is not an instance of n1
    TS_ASSERT(!match(n1, n2, subs));

    n2 = d_nodeManager->mkNode(NONLINEAR_MULT, two, a);

    // should return false for similar operators
    TS_ASSERT(!match(n1, n2, subs));

    n2 = d_nodeManager->mkNode(MULT, two, a, one);

    // should return false for different number of arguments
    TS_ASSERT(!match(n1, n2, subs));

    n1 = x;
    n2 = d_nodeManager->mkConst(true);

    // should return false for different types
    TS_ASSERT(!match(n1, n2, subs));

    n1 = d_nodeManager->mkNode(MULT, x, x);
    n2 = d_nodeManager->mkNode(MULT, two, a);

    // should return false for contradictory substitutions
    TS_ASSERT(!match(n1, n2, subs));

    n2 = d_nodeManager->mkNode(MULT, a, a);
    subs.clear();

    // implementation: check if the cache works correctly
    TS_ASSERT(match(n1, n2, subs));
    TS_ASSERT_EQUALS(subs.size(), 1);
    TS_ASSERT_EQUALS(subs[x], a);
  }
};
