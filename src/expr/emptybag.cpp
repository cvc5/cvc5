/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for empty bags.
 */

#include "expr/emptybag.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const EmptyBag& asa)
{
  return out << "emptybag(" << asa.getType() << ')';
}

size_t EmptyBagHashFunction::operator()(const EmptyBag& es) const
{
  return std::hash<TypeNode>()(es.getType());
}

/**
 * Constructs an emptybag of the specified type. Note that the argument
 * is the type of the bag itself, NOT the type of the elements.
 */
EmptyBag::EmptyBag(const TypeNode& bagType) : d_type(new TypeNode(bagType)) {}

EmptyBag::EmptyBag(const EmptyBag& es) : d_type(new TypeNode(es.getType())) {}

EmptyBag& EmptyBag::operator=(const EmptyBag& es)
{
  (*d_type) = es.getType();
  return *this;
}

EmptyBag::~EmptyBag() {}
const TypeNode& EmptyBag::getType() const { return *d_type; }
bool EmptyBag::operator==(const EmptyBag& es) const
{
  return getType() == es.getType();
}

bool EmptyBag::operator!=(const EmptyBag& es) const { return !(*this == es); }
bool EmptyBag::operator<(const EmptyBag& es) const
{
  return getType() < es.getType();
}

bool EmptyBag::operator<=(const EmptyBag& es) const
{
  return getType() <= es.getType();
}

bool EmptyBag::operator>(const EmptyBag& es) const { return !(*this <= es); }
bool EmptyBag::operator>=(const EmptyBag& es) const { return !(*this < es); }
}  // namespace cvc5::internal
