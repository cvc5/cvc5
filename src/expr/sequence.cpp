/*********************                                                        */
/*! \file sequence.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "expr/sequence.h"

#include <iosfwd>

#include "expr/expr.h"
#include "expr/type.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Sequence& asa) {
  return out << "sequence(" << asa.getType() << ')';
}

size_t SequenceHashFunction::operator()(const Sequence& es) const {
  return TypeHashFunction()(es.getType());
}

/**
 * Constructs an sequence of the specified type. Note that the argument
 * is the type of the set itself, NOT the type of the elements.
 */
Sequence::Sequence(const SequenceType& seqType)
    : d_type(new SequenceType(seqType))
{ }

Sequence::Sequence(const Sequence& es)
    : d_type(new SequenceType(es.getType()))
{ }

Sequence& Sequence::operator=(const Sequence& es) {
  (*d_type) = es.getType();
  return *this;
}

Sequence::~Sequence() { delete d_type; }
const SequenceType& Sequence::getType() const {
  return *d_type;
}
bool Sequence::operator==(const Sequence& es) const
{
  return getType() == es.getType();
}

bool Sequence::operator!=(const Sequence& es) const { return !(*this == es); }
bool Sequence::operator<(const Sequence& es) const
{
  return getType() < es.getType();
}

bool Sequence::operator<=(const Sequence& es) const
{
  return getType() <= es.getType();
}

bool Sequence::operator>(const Sequence& es) const { return !(*this <= es); }
bool Sequence::operator>=(const Sequence& es) const { return !(*this < es); }
}/* CVC4 namespace */
