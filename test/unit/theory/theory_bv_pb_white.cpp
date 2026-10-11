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

#include <sstream>

#include "test_smt.h"
#include "theory/bv/pb/pb_node_manager.h"
#include "theory/bv/pb/pb_types.h"

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
  theory::bv::pb::PbNodeManager pb_nm(d_nodeManager.get());
  Node literal_node = literal.toNode(pb_nm);
  EXPECT_EQ(literal_node.toString(), "x42");
}

TEST_F(TestTheoryBvPbWhite, PbLiteralToNodeInsertion)
{
  theory::bv::pb::PbLiteral literal(42);
  theory::bv::pb::PbNodeManager pb_nm(d_nodeManager.get());
  EXPECT_EQ(pb_nm.countLiterals(), 0);
  literal.toNode(pb_nm);
  EXPECT_EQ(pb_nm.countLiterals(), 1);
}

TEST_F(TestTheoryBvPbWhite, PbLiteralToNodeRecovery)
{
  theory::bv::pb::PbLiteral literal(42);
  theory::bv::pb::PbNodeManager pb_nm(d_nodeManager.get());
  Node literal_node = pb_nm.literalToNode(literal);
  EXPECT_EQ(literal.toNode(pb_nm), literal_node);
}

TEST_F(TestTheoryBvPbWhite, PbConstraintToNodeEquality)
{
  theory::bv::pb::PbNodeManager pb_nm(d_nodeManager.get());

  std::vector<theory::bv::pb::PbLiteral> vars{
      theory::bv::pb::PbLiteral(42),
      theory::bv::pb::PbLiteral(43)};
  std::vector<Integer> coeffs{Integer(3), Integer(5)};

  theory::bv::pb::PbConstraint cons1(
      vars, coeffs, Kind::GEQ, Integer(7), pb_nm, d_nodeManager.get());
  theory::bv::pb::PbConstraint cons2(
      vars, coeffs, Kind::GEQ, Integer(7), pb_nm, d_nodeManager.get());

  EXPECT_EQ(cons1.toNode(), cons2.toNode());
}

TEST_F(TestTheoryBvPbWhite, PbConstraintSetUniqueness)
{
  theory::bv::pb::PbNodeManager pb_nm(d_nodeManager.get());

  std::vector<theory::bv::pb::PbLiteral> vars{
      theory::bv::pb::PbLiteral(42),
      theory::bv::pb::PbLiteral(43)};
  std::vector<Integer> coeffs{Integer(3), Integer(5)};

  theory::bv::pb::PbConstraint cons1(
      vars, coeffs, Kind::GEQ, Integer(7), pb_nm, d_nodeManager.get());
  theory::bv::pb::PbConstraint cons2(
      vars, coeffs, Kind::GEQ, Integer(7), pb_nm, d_nodeManager.get());

  std::set<theory::bv::pb::PbConstraint> constraints{cons1, cons2};
  EXPECT_EQ(constraints.size(), 1);
}

}  // namespace test
}  // namespace cvc5::internal
