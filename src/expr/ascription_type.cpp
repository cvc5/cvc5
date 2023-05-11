/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class representing a type ascription.
 */

#include "expr/ascription_type.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

AscriptionType::AscriptionType(TypeNode t) : d_type(new TypeNode(t)) {}

AscriptionType::AscriptionType(const AscriptionType& at)
    : d_type(new TypeNode(at.getType()))
{
}

AscriptionType& AscriptionType::operator=(const AscriptionType& at)
{
  (*d_type) = at.getType();
  return *this;
}

AscriptionType::~AscriptionType() {}
TypeNode AscriptionType::getType() const { return *d_type.get(); }
bool AscriptionType::operator==(const AscriptionType& other) const
{
  return getType() == other.getType();
}
bool AscriptionType::operator!=(const AscriptionType& other) const
{
  return getType() != other.getType();
}

size_t AscriptionTypeHashFunction::operator()(const AscriptionType& at) const
{
  return std::hash<TypeNode>()(at.getType());
}

std::ostream& operator<<(std::ostream& out, AscriptionType at)
{
  out << at.getType();
  return out;
}

}  // namespace cvc5::internal
