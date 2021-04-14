/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for the strings rewriter.
 */

#include <iostream>
#include <memory>
#include <vector>

#include "expr/node.h"
#include "expr/node_manager.h"
#include "test_smt.h"
#include "theory/rewriter.h"
#include "theory/strings/strings_rewriter.h"

namespace cvc5 {

using namespace kind;
using namespace theory;
using namespace theory::strings;

namespace test {

class TestTheoryWhiteStringsRewriter : public TestSmt
{
};

TEST_F(TestTheoryWhiteStringsRewriter, rewrite_leq)
{
  TypeNode intType = d_nodeManager->integerType();
  TypeNode strType = d_nodeManager->stringType();

  Node a = d_nodeManager->mkConst(::cvc5::String("A"));
  Node bc = d_nodeManager->mkConst(::cvc5::String("BC"));
  Node x = d_nodeManager->mkVar("x", strType);
  Node y = d_nodeManager->mkVar("y", strType);

  Node ax = d_nodeManager->mkNode(STRING_CONCAT, a, x);
  Node bcy = d_nodeManager->mkNode(STRING_CONCAT, bc, y);

  {
    Node leq = d_nodeManager->mkNode(STRING_LEQ, ax, bcy);
    ASSERT_EQ(Rewriter::rewrite(leq), d_nodeManager->mkConst(true));
  }

  {
    Node leq = d_nodeManager->mkNode(STRING_LEQ, bcy, ax);
    ASSERT_EQ(Rewriter::rewrite(leq), d_nodeManager->mkConst(false));
  }
}

}  // namespace test
}  // namespace cvc5
