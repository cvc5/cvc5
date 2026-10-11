/******************************************************************************
 * Top contributors (to current version):
 *   Alan Prado
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implements pseudo-Boolean types and utilities, including:
 * - Enumerations for pseudo-Boolean values and solver states.
 * - Classes for pseudo-Boolean variables and literals.
 * - Classes for pseudo-Boolean constraints and constraint sets, with
 *   constraints stored as Nodes to leverage hash consing.
 */

#include "theory/bv/pb/pb_types.h"

#include <sstream>

#include "theory/bv/pb/pb_node_manager.h"
#include "util/rational.h"
#include "util/string.h"

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

PbVariable::PbVariable(const Integer& id) : d_id(id.toString()) {}

PbVariable::PbVariable(const int& id) : d_id(std::to_string(id)) {}

std::ostream& operator<<(std::ostream& os, const PbVariable& var)
{
  os << "x" << var.d_id;
  return os;
}

bool PbVariable::operator==(const PbVariable& other) const
{
  return this->d_id == other.d_id;
}

PbLiteral::PbLiteral(const PbVariable& var, const bool polarity)
    : d_variable(var), d_polarity(polarity)
{
}

PbLiteral::PbLiteral(const Integer& id, const bool polarity)
    : d_variable(PbVariable(id)), d_polarity(polarity)
{
}

PbLiteral::PbLiteral(const int& id, const bool polarity)
    : d_variable(PbVariable(id)), d_polarity(polarity)
{
}

std::ostream& operator<<(std::ostream& os, const PbLiteral& lit)
{
  os << (lit.d_polarity ? "" : "~") << lit.d_variable;
  return os;
}

bool PbLiteral::operator==(const PbLiteral& other) const
{
  return this->d_variable == other.d_variable
         && this->d_polarity == other.d_polarity;
}

Node PbLiteral::toNode(PbNodeManager& pbNodeManager) const
{
  return pbNodeManager.literalToNode(*this);
}

PbConstraint::PbConstraint(const std::vector<PbLiteral>& literals,
                           const std::vector<Integer>& coefficients,
                           Kind relationalOperator,
                           const Integer& constant,
                           PbNodeManager& pbNodeManager,
                           NodeManager* nodeManager)
{
  std::vector<Node> terms =
      generateProducts(literals, coefficients, pbNodeManager, nodeManager);
  terms.push_back(
      nodeManager->mkConstInt(0));  // Ensure ADD has at least two operands
  Node lhs = nodeManager->mkNode(Kind::ADD, terms);
  Node rhs = nodeManager->mkConstInt(constant);
  d_constraint = nodeManager->mkNode(relationalOperator, lhs, rhs);
}

PbConstraint::PbConstraint(const PbLiteral& literal,
                           const Integer& coefficient,
                           Kind relationalOperator,
                           const Integer& constant,
                           PbNodeManager& pbNodeManager,
                           NodeManager* nodeManager)
{
  Node term = nodeManager->mkNode(Kind::MULT,
                                  nodeManager->mkConstInt(coefficient),
                                  literal.toNode(pbNodeManager));
  Node lhs = nodeManager->mkNode(
      Kind::ADD,
      term,
      nodeManager->mkConstInt(0));  // Ensure ADD has at least two operands
  Node rhs = nodeManager->mkConstInt(constant);
  d_constraint = nodeManager->mkNode(relationalOperator, lhs, rhs);
}

std::vector<Node> PbConstraint::generateProducts(
    const std::vector<PbLiteral>& literals,
    const std::vector<Integer>& coefficients,
    PbNodeManager& pbNodeManager,
    NodeManager* nodeManager)
{
  Assert(literals.size() == coefficients.size());

  auto createTerm = [&nodeManager, &pbNodeManager](const PbLiteral& lit,
                                                   const Integer& coef) {
    return nodeManager->mkNode(
        Kind::MULT, nodeManager->mkConstInt(coef), lit.toNode(pbNodeManager));
  };

  std::vector<Node> terms(literals.size());
  std::transform(literals.begin(),
                 literals.end(),
                 coefficients.begin(),
                 terms.begin(),
                 createTerm);
  return terms;
}

std::ostream& operator<<(std::ostream& os, const PbConstraint& lit)
{
  os << lit.toNode();
  return os;
}

bool PbConstraint::operator==(const PbConstraint& other) const
{
  return this->d_constraint == other.d_constraint;
}

bool PbConstraint::operator<(const PbConstraint& other) const
{
  return this->d_constraint < other.d_constraint;
}

Node PbConstraint::toNode() const { return d_constraint; }

PbConstraintSet::PbConstraintSet(const std::set<PbConstraint> constraints,
                                 NodeManager* nm)
{
  std::vector<Node> constraint_vector(constraints.size());
  std::transform(constraints.begin(),
                 constraints.end(),
                 constraint_vector.begin(),
                 [](const PbConstraint& x) { return x.toNode(); });
  d_constraintSet = nm->mkNode(Kind::SEXPR, constraint_vector);
}

}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
