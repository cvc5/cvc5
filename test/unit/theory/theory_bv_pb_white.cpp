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
#include "theory/bv/pb/pb_node_manager.h"

namespace cvc5::internal {

namespace test {

class TestTheoryBvPbWhite : public TestSmt
{
};

TEST_F(TestTheoryBvPbWhite, PbVariableEqualsString)
{
  theory::bv::pb::PbVariable variable(42);
  std::string variable_string = (std::ostringstream() << variable).str();
  EXPECT_EQ(variable_string, "x42");
}

TEST_F(TestTheoryBvPbWhite, PbLiteralEqualsString)
{
  theory::bv::pb::PbLiteral literal(42);
  std::string literal_string = (std::ostringstream() << literal).str();
  EXPECT_EQ(literal_string, "x42");
}

TEST_F(TestTheoryBvPbWhite, PbLiteralNegativeEqualsString)
{
  theory::bv::pb::PbLiteral literal(42, false);
  std::string literal_string = (std::ostringstream() << literal).str();
  EXPECT_EQ(literal_string, "~x42");
}

TEST_F(TestTheoryBvPbWhite, PbLiteralToNodeEqualsString)
{
  theory::bv::pb::PbLiteral literal(42);
  theory::bv::pb::PbNodeManager pb_nm(d_nodeManager);
  Node literal_node = literal.toNode(pb_nm);
  EXPECT_EQ(literal_node.toString(), "x42");
}

TEST_F(TestTheoryBvPbWhite, PbLiteralToNodeInsertion)
{
  theory::bv::pb::PbLiteral literal(42);
  theory::bv::pb::PbNodeManager pb_nm(d_nodeManager);
  EXPECT_EQ(pb_nm.countLiterals(), 0);
  literal.toNode(pb_nm);
  EXPECT_EQ(pb_nm.countLiterals(), 1);
}

TEST_F(TestTheoryBvPbWhite, PbLiteralToNodeRecovery)
{
  theory::bv::pb::PbLiteral literal(42);
  theory::bv::pb::PbNodeManager pb_nm(d_nodeManager);
  Node literal_node = pb_nm.literalToNode(literal);
  EXPECT_EQ(literal.toNode(pb_nm), literal_node);
}

}  // namespace test
}  // namespace cvc5::internal
