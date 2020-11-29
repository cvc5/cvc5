/*********************                                                        */
/*! \file abstract_value.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of abstract values
 **
 ** Representation of abstract values.
 **/

#include "cvc4_public.h"

#pragma once

#include <iosfwd>

#include "util/integer.h"

namespace CVC4 {

class CVC4_PUBLIC AbstractValue {
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
};/* class AbstractValue */

std::ostream& operator<<(std::ostream& out, const AbstractValue& val) CVC4_PUBLIC;

/**
 * Hash function for the BitVector constants.
 */
struct CVC4_PUBLIC AbstractValueHashFunction {
  inline size_t operator()(const AbstractValue& val) const {
    return IntegerHashFunction()(val.getIndex());
  }
};/* struct AbstractValueHashFunction */

}/* CVC4 namespace */
