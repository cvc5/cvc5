/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of a constant array (an array in which the element is the
 * same for all indices).
 */

#include "cvc5_public.h"

#ifndef CVC5__EXPR__ARRAY_STORE_ALL_H
#define CVC5__EXPR__ARRAY_STORE_ALL_H

#include <iosfwd>
#include <memory>

namespace cvc5::internal {

template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;
class TypeNode;

class ArrayStoreAll
{
 public:
  /**
   * @throws IllegalArgumentException if `type` is not an array or if `expr` is
   * not a constant of type `type`.
   */
  ArrayStoreAll(const TypeNode& type, const Node& value);
  ~ArrayStoreAll();

  ArrayStoreAll(const ArrayStoreAll& other);
  ArrayStoreAll& operator=(const ArrayStoreAll& other);

  const TypeNode& getType() const;
  const Node& getValue() const;

  bool operator==(const ArrayStoreAll& asa) const;
  bool operator!=(const ArrayStoreAll& asa) const;
  bool operator<(const ArrayStoreAll& asa) const;
  bool operator<=(const ArrayStoreAll& asa) const;
  bool operator>(const ArrayStoreAll& asa) const;
  bool operator>=(const ArrayStoreAll& asa) const;

 private:
  std::unique_ptr<TypeNode> d_type;
  std::unique_ptr<Node> d_value;
}; /* class ArrayStoreAll */

std::ostream& operator<<(std::ostream& out, const ArrayStoreAll& asa);

/**
 * Hash function for the ArrayStoreAll constants.
 */
struct ArrayStoreAllHashFunction
{
  size_t operator()(const ArrayStoreAll& asa) const;
}; /* struct ArrayStoreAllHashFunction */

}  // namespace cvc5::internal

#endif /* CVC5__ARRAY_STORE_ALL_H */
