/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
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

std::ostream& operator<<(std::ostream& out, const SortToTerm& asa)
{
  return out << "sort_to_term(" << asa.getType() << ')';
}

size_t SortToTermHashFunction::operator()(const SortToTerm& stt) const
{
  return std::hash<TypeNode>()(stt.getType());
}

SortToTerm::SortToTerm(const TypeNode& sort) : d_type(new TypeNode(sort))
{
}

SortToTerm::SortToTerm(const SortToTerm& stt)
    : d_type(new TypeNode(stt.getType()))
{
}

SortToTerm::~SortToTerm() {}

const TypeNode& SortToTerm::getType() const { return *d_type; }

bool SortToTerm::operator==(const SortToTerm& stt) const
{
  return getType() == stt.getType();
}

}  // namespace cvc5::internal
