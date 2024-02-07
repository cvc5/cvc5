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
 * Payload that represents a sort to be represented as a term.
 */

#include "expr/sort_to_term.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const SortToTerm& asa) {
  return out << "sort_to_term(" << asa.getType() << ')';
}

size_t SortToTermHashFunction::operator()(const SortToTerm& es) const {
  return std::hash<TypeNode>()(es.getType());
}

SortToTerm::SortToTerm(const TypeNode& setType) : d_type(new TypeNode(setType)) {}

SortToTerm::SortToTerm(const SortToTerm& es) : d_type(new TypeNode(es.getType())) {}

SortToTerm::~SortToTerm() {}

const TypeNode& SortToTerm::getType() const { return *d_type; }

}  // namespace cvc5::internal
