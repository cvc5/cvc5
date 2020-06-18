/*********************                                                        */
/*! \file uninterpreted_constant.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of constants of uninterpreted sorts
 **
 ** Representation of constants of uninterpreted sorts.
 **/

#include "cvc4_public.h"

#pragma once

#include <iosfwd>

#include "expr/type.h"

namespace CVC4 {

class CVC4_PUBLIC UninterpretedConstant {
 public:
  UninterpretedConstant(Type type, Integer index);

  Type getType() const { return d_type; }
  const Integer& getIndex() const { return d_index; }
  bool operator==(const UninterpretedConstant& uc) const
  {
    return d_type == uc.d_type && d_index == uc.d_index;
  }
  bool operator!=(const UninterpretedConstant& uc) const
  {
    return !(*this == uc);
  }

  bool operator<(const UninterpretedConstant& uc) const
  {
    return d_type < uc.d_type ||
           (d_type == uc.d_type && d_index < uc.d_index);
  }
  bool operator<=(const UninterpretedConstant& uc) const
  {
    return d_type < uc.d_type ||
           (d_type == uc.d_type && d_index <= uc.d_index);
  }
  bool operator>(const UninterpretedConstant& uc) const
  {
    return !(*this <= uc);
  }
  bool operator>=(const UninterpretedConstant& uc) const
  {
    return !(*this < uc);
  }

 private:
  const Type d_type;
  const Integer d_index;
};/* class UninterpretedConstant */

std::ostream& operator<<(std::ostream& out, const UninterpretedConstant& uc) CVC4_PUBLIC;

/**
 * Hash function for the BitVector constants.
 */
struct CVC4_PUBLIC UninterpretedConstantHashFunction {
  inline size_t operator()(const UninterpretedConstant& uc) const {
    return TypeHashFunction()(uc.getType()) * IntegerHashFunction()(uc.getIndex());
  }
};/* struct UninterpretedConstantHashFunction */

}/* CVC4 namespace */
