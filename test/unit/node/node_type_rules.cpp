/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of type rules for cvc5::Node.
 */

#include <cvc5/cvc5.h>

#include <algorithm>
#include <sstream>
#include <string>
#include <vector>

#include "expr/node_manager.h"
#include "expr/type_node.h"
#include "test_node.h"
#include "util/rational.h"

namespace cvc5::internal {
namespace test {

class TestNodeTestRules : public TestNode
{
 protected:
  TypeNode getTypeConcat(const Node& a, const Node& b)
  {
    NodeManager* nm = NodeManager::currentNM();
    Node c = nm->mkNode(Kind::STRING_CONCAT, a, b);
    return c.getTypeOrNull(true);
  }
};

TEST_F(TestNodeTestRules, gradual_types)
{
  NodeManager* nm = NodeManager::currentNM();
  TypeNode at = nm->mkAbstractType(Kind::ABSTRACT_TYPE);
  TypeNode aseqt = nm->mkAbstractType(Kind::SEQUENCE_TYPE);
  TypeNode intt = nm->integerType();
  TypeNode sit = nm->mkSequenceType(intt);

  SkolemManager* sm = nm->getSkolemManager();
  Node kat = sm->mkDummySkolem("kat", at);
  Node kaseqt = sm->mkDummySkolem("kaseqt", aseqt);
  Node ksit = sm->mkDummySkolem("ksit", sit);
  Node one = nm->mkConstInt(Rational(1));

  TypeNode t1 = getTypeConcat(kat, kat);
  ASSERT_TRUE(t1 == at);
  TypeNode t2 = getTypeConcat(kat, kaseqt);
  ASSERT_TRUE(t2 == aseqt);
  TypeNode t3 = getTypeConcat(kat, ksit);
  ASSERT_TRUE(t3 == sit);
  TypeNode t4 = getTypeConcat(kat, one);
  ASSERT_TRUE(t4.isNull());
}

}  // namespace test
}  // namespace cvc5::internal
