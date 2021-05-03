/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of constants of uninterpreted sorts.
 */

#include "cvc5_public.h"

#ifndef CVC5__UNINTERPRETED_CONSTANT_H
#define CVC5__UNINTERPRETED_CONSTANT_H

#include <iosfwd>
#include <memory>

#include "util/integer.h"

namespace cvc5 {

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
struct UninterpretedConstantHashFunction
{
  size_t operator()(const UninterpretedConstant& uc) const;
}; /* struct UninterpretedConstantHashFunction */

}  // namespace cvc5

#endif /* CVC5__UNINTERPRETED_CONSTANT_H */
