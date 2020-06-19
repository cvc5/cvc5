/*********************                                                        */
/*! \file array_store_all.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
// messy; Expr needs ArrayStoreAll (because it's the payload of a
// CONSTANT-kinded expression), and ArrayStoreAll needs Expr.
class Expr;
class ArrayType;
}  // namespace CVC4

namespace CVC4 {

class CVC4_PUBLIC ArrayStoreAll {
 public:
  /**
   * @throws IllegalArgumentException if `type` is not an array or if `expr` is
   * not a constant of type `type`.
   */
  ArrayStoreAll(const ArrayType& type, const Expr& expr);
  ~ArrayStoreAll();

  ArrayStoreAll(const ArrayStoreAll& other);
  ArrayStoreAll& operator=(const ArrayStoreAll& other);

  const ArrayType& getType() const;
  const Expr& getExpr() const;

  bool operator==(const ArrayStoreAll& asa) const;
  bool operator!=(const ArrayStoreAll& asa) const;
  bool operator<(const ArrayStoreAll& asa) const;
  bool operator<=(const ArrayStoreAll& asa) const;
  bool operator>(const ArrayStoreAll& asa) const;
  bool operator>=(const ArrayStoreAll& asa) const;

 private:
  std::unique_ptr<ArrayType> d_type;
  std::unique_ptr<Expr> d_expr;
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
