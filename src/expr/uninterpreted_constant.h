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

#ifndef CVC4__UNINTERPRETED_CONSTANT_H
#define CVC4__UNINTERPRETED_CONSTANT_H

#include <iosfwd>
#include <memory>

#include "util/integer.h"

namespace CVC4 {

class TypeNode;

class UninterpretedConstant
{
 public:
  UninterpretedConstant(const TypeNode& type, Integer index);
  ~UninterpretedConstant();

  UninterpretedConstant(const UninterpretedConstant& other);

  const TypeNode& getType() const;
  const Integer& getIndex() const;
  bool operator==(const UninterpretedConstant& uc) const;
  bool operator!=(const UninterpretedConstant& uc) const;
  bool operator<(const UninterpretedConstant& uc) const;
  bool operator<=(const UninterpretedConstant& uc) const;
  bool operator>(const UninterpretedConstant& uc) const;
  bool operator>=(const UninterpretedConstant& uc) const;

 private:
  std::unique_ptr<TypeNode> d_type;
  const Integer d_index;
}; /* class UninterpretedConstant */

std::ostream& operator<<(std::ostream& out, const UninterpretedConstant& uc);

/**
 * Hash function for the BitVector constants.
 */
struct CVC4_PUBLIC UninterpretedConstantHashFunction
{
  size_t operator()(const UninterpretedConstant& uc) const;
}; /* struct UninterpretedConstantHashFunction */

}  // namespace CVC4

#endif /* CVC4__UNINTERPRETED_CONSTANT_H */
