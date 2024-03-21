/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Kshitij Bansal, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Payload class for empty sets.
 */

#include "expr/emptyset.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const EmptySet& asa) {
  return out << "emptyset(" << asa.getType() << ')';
}

size_t EmptySetHashFunction::operator()(const EmptySet& es) const {
  return std::hash<TypeNode>()(es.getType());
}

/**
 * Constructs an emptyset of the specified type. Note that the argument
 * is the type of the set itself, NOT the type of the elements.
 */
EmptySet::EmptySet(const TypeNode& setType) : d_type(new TypeNode(setType)) {}

EmptySet::EmptySet(const EmptySet& es) : d_type(new TypeNode(es.getType())) {}

EmptySet& EmptySet::operator=(const EmptySet& es) {
  (*d_type) = es.getType();
  return *this;
}

EmptySet::~EmptySet() {}
const TypeNode& EmptySet::getType() const { return *d_type; }
bool EmptySet::operator==(const EmptySet& es) const
{
  return getType() == es.getType();
}
}  // namespace cvc5::internal
