/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for the string utils
 */

#include <unordered_set>
#include <vector>

#include "expr/node.h"
#include "test_node.h"
#include "theory/strings/theory_strings_utils.h"
#include "util/string.h"

namespace cvc5::internal {

using namespace kind;
using namespace theory;
using namespace theory::strings;

namespace test {

class TestTheoryWhiteStringsUtils : public TestNode
{
};

TEST_F(TestTheoryWhiteStringsUtils, collect_empty_eqs)
{
  TypeNode strType = d_nodeManager->stringType();

  Node empty = d_nodeManager->mkConst(String(""));
  Node a = d_nodeManager->mkConst(String("A"));
  Node x = d_nodeManager->mkVar("x", strType);

  Node emptyEqX = empty.eqNode(x);
  Node emptyEqA = a.eqNode(empty);
  Node xEqA = x.eqNode(a);

  std::vector<Node> emptyNodes;
  bool allEmptyEqs;
  std::unordered_set<Node> expected = {a, x};

  std::tie(allEmptyEqs, emptyNodes) =
      utils::collectEmptyEqs(d_nodeManager->mkNode(AND, emptyEqX, emptyEqA));
  ASSERT_TRUE(allEmptyEqs);
  ASSERT_EQ(std::unordered_set<Node>(emptyNodes.begin(), emptyNodes.end()),
            expected);

  std::tie(allEmptyEqs, emptyNodes) = utils::collectEmptyEqs(
      d_nodeManager->mkNode(AND, emptyEqX, xEqA, emptyEqA));
  ASSERT_FALSE(allEmptyEqs);
  ASSERT_EQ(std::unordered_set<Node>(emptyNodes.begin(), emptyNodes.end()),
            expected);
}

}  // namespace test
}  // namespace cvc5::internal
