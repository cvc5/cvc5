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

#include <sstream>

namespace cvc5::internal {
namespace theory {
namespace bv {
namespace pb {

PbVariable::PbVariable(const Integer& id) : id(id.toString()) {}

PbVariable::PbVariable(const int& id) : id(std::to_string(id)) {}

std::ostream& operator<<(std::ostream& os, const PbVariable& var)
{
  os << "x" << var.id;
  return os;
}

PbLiteral::PbLiteral(const PbVariable& var, const bool p)
    : variable(var), polarity(p) {}

PbLiteral::PbLiteral(const Integer& id, const bool p)
    : variable(PbVariable(id)), polarity(p) {}

PbLiteral::PbLiteral(const int& id, const bool p)
    : variable(PbVariable(id)), polarity(p) {}

std::ostream& operator<<(std::ostream& os, const PbLiteral& lit)
{
  os << (lit.polarity ? "" : "~") << lit.variable;
  return os;
}

Node PbLiteral::toNode(NodeManager* nm) const
{
  return nm->mkBoundVar((std::ostringstream() << this).str(),
                        nm->booleanType());
}

PbConstraint::PbConstraint(const std::vector<PbLiteral>& literals,
                           const std::vector<Integer>& coefficients,
                           Kind relationalOperator,
                           const Integer& constant,
                           NodeManager* nm)
{
  std::vector<Node> terms = generateProducts(literals, coefficients, nm);
  terms.push_back(nm->mkConstInt(0));  // Ensure ADD has at least two operands
  Node lhs = nm->mkNode(Kind::ADD, terms);
  Node rhs = nm->mkConstInt(constant);
  constraint = nm->mkNode(relationalOperator, lhs, rhs);
}

PbConstraint::PbConstraint(const PbLiteral& literal,
                           const Integer& coefficient,
                           Kind relationalOperator,
                           const Integer& constant,
                           NodeManager* nm)
{
  Node term = nm->mkNode(Kind::MULT,
                         nm->mkConstInt(coefficient),
                         literal.toNode(nm));
  Node lhs = nm->mkNode(Kind::ADD, term, nm->mkConstInt(0)); // Ensure ADD has at least two operands
  Node rhs = nm->mkConstInt(constant);
  constraint = nm->mkNode(relationalOperator, lhs, rhs);
}

std::vector<Node> PbConstraint::generateProducts(
    const std::vector<PbLiteral>& literals,
    const std::vector<Integer>& coefficients,
    NodeManager* nm)
{
  Assert(literals.size() == coefficients.size());

  auto createTerm = [&nm](const PbLiteral& lit, const Integer& coef) {
    return nm->mkNode(Kind::MULT,
                      nm->mkConstInt(coef),
                      lit.toNode(nm));
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
  return constraint;
}

PbConstraintSet::PbConstraintSet(const std::set<PbConstraint> constraints,
                                 NodeManager* nm)
{
  std::vector<Node> constraint_vector(constraints.size());
  std::transform(constraints.begin(),
                 constraints.end(),
                 constraint_vector.begin(),
                 [](PbConstraint& x) { return x.toNode(); });
  constraintSet = nm->mkNode(Kind::SEXPR, constraint_vector);
}


}  // namespace pb
}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
