/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of abstract values.
 */

#include "cvc5_public.h"

#pragma once

#include <iosfwd>

#include "util/integer.h"

namespace cvc5 {

class AbstractValue
{
  const Integer d_index;

 public:
  AbstractValue(Integer index);

  const Integer& getIndex() const { return d_index; }
  bool operator==(const AbstractValue& val) const
  {
    return d_index == val.d_index;
  }
  bool operator!=(const AbstractValue& val) const { return !(*this == val); }
  bool operator<(const AbstractValue& val) const
  {
    return d_index < val.d_index;
  }
  bool operator<=(const AbstractValue& val) const
  {
    return d_index <= val.d_index;
  }
  bool operator>(const AbstractValue& val) const { return !(*this <= val); }
  bool operator>=(const AbstractValue& val) const { return !(*this < val); }
}; /* class AbstractValue */

std::ostream& operator<<(std::ostream& out, const AbstractValue& val);

/**
 * Hash function for the BitVector constants.
 */
struct AbstractValueHashFunction
{
  inline size_t operator()(const AbstractValue& val) const {
    return IntegerHashFunction()(val.getIndex());
  }
}; /* struct AbstractValueHashFunction */

}  // namespace cvc5
