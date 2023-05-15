/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for representing abstract types.
 */

#include "theory/builtin/abstract_type.h"

#include <iostream>

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const AbstractType& op)
{
  return out << "(AbstractType " << op.getKind() << ')';
}

size_t AbstractTypeHashFunction::operator()(const AbstractType& op) const
{
  return kind::KindHashFunction()(op.getKind());
}

AbstractType::AbstractType(Kind k) : d_kind(k) {}

AbstractType::AbstractType(const AbstractType& op) : d_kind(op.getKind()) {}

Kind AbstractType::getKind() const { return d_kind; }

bool AbstractType::operator==(const AbstractType& op) const
{
  return getKind() == op.getKind();
}

}  // namespace cvc5::internal
