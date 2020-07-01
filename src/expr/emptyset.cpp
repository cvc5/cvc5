/*********************                                                        */
/*! \file emptyset.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Kshitij Bansal
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "expr/emptyset.h"

#include <iosfwd>

#include "expr/expr.h"
#include "expr/type.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const EmptySet& asa) {
  return out << "emptyset(" << asa.getType() << ')';
}

size_t EmptySetHashFunction::operator()(const EmptySet& es) const {
  return TypeHashFunction()(es.getType());
}

/**
 * Constructs an emptyset of the specified type. Note that the argument
 * is the type of the set itself, NOT the type of the elements.
 */
EmptySet::EmptySet(const SetType& setType)
    : d_type(new SetType(setType))
{ }

EmptySet::EmptySet(const EmptySet& es)
    : d_type(new SetType(es.getType()))
{ }

EmptySet& EmptySet::operator=(const EmptySet& es) {
  (*d_type) = es.getType();
  return *this;
}

EmptySet::~EmptySet() { delete d_type; }
const SetType& EmptySet::getType() const {
  return *d_type;
}
bool EmptySet::operator==(const EmptySet& es) const
{
  return getType() == es.getType();
}

bool EmptySet::operator!=(const EmptySet& es) const { return !(*this == es); }
bool EmptySet::operator<(const EmptySet& es) const
{
  return getType() < es.getType();
}

bool EmptySet::operator<=(const EmptySet& es) const
{
  return getType() <= es.getType();
}

bool EmptySet::operator>(const EmptySet& es) const { return !(*this <= es); }
bool EmptySet::operator>=(const EmptySet& es) const { return !(*this < es); }
}/* CVC4 namespace */
