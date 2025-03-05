/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Unit tests for PB-Blasting
 */

#include<sstream>

#include "test_smt.h"
#include "theory/bv/pb/pb_types.h"

namespace cvc5::internal {

namespace test {

class TestTheoryBvPbWhite : public TestSmt
{
};

TEST_F(TestTheoryBvPbWhite, PbVariableEqualsString)
{
  theory::bv::pb::PbVariable variable(42);
  std::string variableString = (std::ostringstream() << variable).str();
  EXPECT_EQ(variableString, "x42");
}

TEST_F(TestTheoryBvPbWhite, PbLiteralEqualsString)
{
  theory::bv::pb::PbLiteral literal(42);
  std::string literalString = (std::ostringstream() << literal).str();
  EXPECT_EQ(literalString, "x42");
}

TEST_F(TestTheoryBvPbWhite, PbLiteralNegativeEqualsString)
{
  theory::bv::pb::PbLiteral literal(42, false);
  std::string literalString = (std::ostringstream() << literal).str();
  EXPECT_EQ(literalString, "~x42");
}

TEST_F(TestTheoryBvPbWhite, PbLiteralToNodeEqualsString)
{
  theory::bv::pb::PbLiteral literal(42);
  theory::bv::pb::PbLiteralToNodeMap map;
  Node literalNode = literal.toNode(map, d_nodeManager);
  EXPECT_EQ(literalNode.toString(), "x42");
}

TEST_F(TestTheoryBvPbWhite, PbLiteralToNodeInsertion)
{
  theory::bv::pb::PbLiteral literal(42);
  theory::bv::pb::PbLiteralToNodeMap map;
  Node literalNode = literal.toNode(map, d_nodeManager);
  EXPECT_TRUE(map.count(literal));
  EXPECT_EQ(map[literal], literalNode);
}

TEST_F(TestTheoryBvPbWhite, PbLiteralToNodeRecovery)
{
  theory::bv::pb::PbLiteral literal(42);
  Node literalNode = d_nodeManager->mkBoundVar(
      (std::ostringstream() << literal).str(), d_nodeManager->booleanType());
  theory::bv::pb::PbLiteralToNodeMap map;
  map[literal] = literalNode;
  EXPECT_EQ(literal.toNode(map, d_nodeManager), literalNode);
}

}  // namespace test
}  // namespace cvc5::internal
