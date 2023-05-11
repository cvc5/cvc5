/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Mathias Preiner, Aina Niemetz
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

#include "cvc5_public.h"

#ifndef CVC5__EMPTY_BAG_H
#define CVC5__EMPTY_BAG_H

#include <iosfwd>
#include <memory>

namespace cvc5::internal {

class TypeNode;

class EmptyBag
{
 public:
  /**
   * Constructs an emptybag of the specified type. Note that the argument
   * is the type of the bag itself, NOT the type of the elements.
   */
  EmptyBag(const TypeNode& bagType);
  ~EmptyBag();
  EmptyBag(const EmptyBag& other);
  EmptyBag& operator=(const EmptyBag& other);

  const TypeNode& getType() const;
  bool operator==(const EmptyBag& es) const;
  bool operator!=(const EmptyBag& es) const;
  bool operator<(const EmptyBag& es) const;
  bool operator<=(const EmptyBag& es) const;
  bool operator>(const EmptyBag& es) const;
  bool operator>=(const EmptyBag& es) const;

 private:
  EmptyBag();

  /** the type of the empty bag itself (not the type of the elements)*/
  std::unique_ptr<TypeNode> d_type;
}; /* class EmptyBag */

std::ostream& operator<<(std::ostream& out, const EmptyBag& es);

struct EmptyBagHashFunction
{
  size_t operator()(const EmptyBag& es) const;
}; /* struct EmptyBagHashFunction */

}  // namespace cvc5::internal

#endif /* CVC5__EMPTY_BAG_H */
