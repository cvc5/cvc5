/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Kshitij Bansal, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "cvc5_public.h"

#ifndef CVC5__EMPTY_SET_H
#define CVC5__EMPTY_SET_H

#include <iosfwd>
#include <memory>

namespace cvc5::internal {

class TypeNode;

class EmptySet
{
 public:
  /**
   * Constructs an emptyset of the specified type. Note that the argument
   * is the type of the set itself, NOT the type of the elements.
   */
  EmptySet(const TypeNode& setType);
  ~EmptySet();
  EmptySet(const EmptySet& other);
  EmptySet& operator=(const EmptySet& other);

  const TypeNode& getType() const;
  bool operator==(const EmptySet& es) const;
  bool operator!=(const EmptySet& es) const;
  bool operator<(const EmptySet& es) const;
  bool operator<=(const EmptySet& es) const;
  bool operator>(const EmptySet& es) const;
  bool operator>=(const EmptySet& es) const;

 private:
  EmptySet();

  std::unique_ptr<TypeNode> d_type;
}; /* class EmptySet */

std::ostream& operator<<(std::ostream& out, const EmptySet& es);

struct EmptySetHashFunction
{
  size_t operator()(const EmptySet& es) const;
}; /* struct EmptySetHashFunction */

}  // namespace cvc5::internal

#endif /* CVC5__EMPTY_SET_H */
