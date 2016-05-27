/*********************                                                        */
/*! \file array_store_all.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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

#pragma once

#include <iosfwd>

#include "base/exception.h"

namespace CVC4 {
  // messy; Expr needs ArrayStoreAll (because it's the payload of a
  // CONSTANT-kinded expression), and ArrayStoreAll needs Expr.
  class Expr;
  class ArrayType;
}/* CVC4 namespace */


namespace CVC4 {

class CVC4_PUBLIC ArrayStoreAll {
public:
  ArrayStoreAll(const ArrayStoreAll& other);

  ArrayStoreAll& operator=(const ArrayStoreAll& other);

  ArrayStoreAll(const ArrayType& type, const Expr& expr)
      throw(IllegalArgumentException);

  ~ArrayStoreAll() throw();

  const ArrayType& getType() const throw();

  const Expr& getExpr() const throw();

  bool operator==(const ArrayStoreAll& asa) const throw();

  bool operator!=(const ArrayStoreAll& asa) const throw() {
    return !(*this == asa);
  }

  bool operator<(const ArrayStoreAll& asa) const throw();
  bool operator<=(const ArrayStoreAll& asa) const throw();
  bool operator>(const ArrayStoreAll& asa) const throw() {
    return !(*this <= asa);
  }
  bool operator>=(const ArrayStoreAll& asa) const throw() {
    return !(*this < asa);
  }

private:
  ArrayType* d_type;
  Expr* d_expr;
};/* class ArrayStoreAll */

std::ostream& operator<<(std::ostream& out, const ArrayStoreAll& asa) CVC4_PUBLIC;

/**
 * Hash function for the ArrayStoreAll constants.
 */
struct CVC4_PUBLIC ArrayStoreAllHashFunction {
  size_t operator()(const ArrayStoreAll& asa) const;
};/* struct ArrayStoreAllHashFunction */

}/* CVC4 namespace */
