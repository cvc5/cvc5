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
#include "util/rational.h"
#include "util/string.h"

#include <sstream>

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

PbLiteral::PbLiteral(const PbVariable& var, const bool p)
    : d_variable(var), d_polarity(p) {}

PbLiteral::PbLiteral(const Integer& id, const bool p)
    : d_variable(PbVariable(id)), d_polarity(p) {}

PbLiteral::PbLiteral(const int& id, const bool p)
    : d_variable(PbVariable(id)), d_polarity(p) {}

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

Node PbLiteral::toNode(PbLiteralToNodeMap& map, NodeManager* nm) const
{
  return map
      .try_emplace(*this,
                   nm->mkBoundVar((std::ostringstream() << *this).str(),
                                  nm->booleanType()))
      .first->second;
}

PbConstraint::PbConstraint(const std::vector<PbLiteral>& literals,
                           const std::vector<Integer>& coefficients,
                           Kind relationalOperator,
                           const Integer& constant,
                           PbLiteralToNodeMap& map,
                           NodeManager* nm)
{
  std::vector<Node> terms = generateProducts(literals, coefficients, map, nm);
  terms.push_back(nm->mkConstInt(0));  // Ensure ADD has at least two operands
  Node lhs = nm->mkNode(Kind::ADD, terms);
  Node rhs = nm->mkConstInt(constant);
  d_constraint = nm->mkNode(relationalOperator, lhs, rhs);
}

PbConstraint::PbConstraint(const PbLiteral& literal,
                           const Integer& coefficient,
                           Kind relationalOperator,
                           const Integer& constant,
                           PbLiteralToNodeMap& map,
                           NodeManager* nm)
{
  Node term = nm->mkNode(
      Kind::MULT, nm->mkConstInt(coefficient), literal.toNode(map, nm));
  Node lhs =
      nm->mkNode(Kind::ADD,
                 term,
                 nm->mkConstInt(0));  // Ensure ADD has at least two operands
  Node rhs = nm->mkConstInt(constant);
  d_constraint = nm->mkNode(relationalOperator, lhs, rhs);
}

std::vector<Node> PbConstraint::generateProducts(
    const std::vector<PbLiteral>& literals,
    const std::vector<Integer>& coefficients,
    PbLiteralToNodeMap& map,
    NodeManager* nm)
{
  Assert(literals.size() == coefficients.size());

  auto createTerm = [&nm, &map](const PbLiteral& lit, const Integer& coef) {
    return nm->mkNode(Kind::MULT,
                      nm->mkConstInt(coef),
                      lit.toNode(map, nm));
  };

  std::vector<Node> terms(literals.size());
  std::transform(literals.begin(),
                 literals.end(),
                 coefficients.begin(),
                 terms.begin(),
                 createTerm);
  return terms;
}

Node PbConstraint::toNode() const
{
  return d_constraint;
}

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
