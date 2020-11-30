/*********************                                                        */
/*! \file array_store_all.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of a constant array (an array in which the
 ** element is the same for all indices)
 **
 ** Representation of a constant array (an array in which the element is
 ** the same for all indices).
 **/

#include "cvc4_public.h"

#ifndef CVC4__ARRAY_STORE_ALL_H
#define CVC4__ARRAY_STORE_ALL_H

#include <iosfwd>
#include <memory>


namespace CVC4 {

template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;
class TypeNode;

class CVC4_PUBLIC ArrayStoreAll {
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

std::ostream& operator<<(std::ostream& out,
                         const ArrayStoreAll& asa) CVC4_PUBLIC;

/**
 * Hash function for the ArrayStoreAll constants.
 */
struct CVC4_PUBLIC ArrayStoreAllHashFunction {
  size_t operator()(const ArrayStoreAll& asa) const;
}; /* struct ArrayStoreAllHashFunction */

}  // namespace CVC4

#endif /* CVC4__ARRAY_STORE_ALL_H */
