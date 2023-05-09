/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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
#include <memory>

#include "util/integer.h"

namespace cvc5::internal {

class TypeNode;

class UninterpretedSortValue
{
 public:
  UninterpretedSortValue(const TypeNode& type, const Integer& index);
  UninterpretedSortValue(const UninterpretedSortValue& val);
  ~UninterpretedSortValue();

  const Integer& getIndex() const { return d_index; }
  const TypeNode& getType() const;

  bool operator==(const UninterpretedSortValue& val) const;
  bool operator!=(const UninterpretedSortValue& val) const
  {
    return !(*this == val);
  }
  bool operator<(const UninterpretedSortValue& val) const;
  bool operator<=(const UninterpretedSortValue& val) const;
  bool operator>(const UninterpretedSortValue& val) const
  {
    return !(*this <= val);
  }
  bool operator>=(const UninterpretedSortValue& val) const
  {
    return !(*this < val);
  }

 private:
  /** The type of the abstract value */
  std::unique_ptr<TypeNode> d_type;
  /** The index of the abstract value */
  const Integer d_index;
}; /* class UninterpretedSortValue */

std::ostream& operator<<(std::ostream& out, const UninterpretedSortValue& val);

/**
 * Hash function for abstract values.
 */
struct UninterpretedSortValueHashFunction
{
  inline size_t operator()(const UninterpretedSortValue& val) const
  {
    return IntegerHashFunction()(val.getIndex());
  }
}; /* struct UninterpretedSortValueHashFunction */

}  // namespace cvc5::internal
