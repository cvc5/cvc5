/*********************                                                        */
/*! \file array_store_all.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of a constant array (an array in which the
 ** element is the same for all indices)
 **
 ** Representation of a constant array (an array in which the element is
 ** the same for all indices).
 **/

#include "cvc4_public.h"

#pragma once

namespace CVC4 {
  // messy; Expr needs ArrayStoreAll (because it's the payload of a
  // CONSTANT-kinded expression), and ArrayStoreAll needs Expr.
  class CVC4_PUBLIC ArrayStoreAll;
}/* CVC4 namespace */

#include "expr/expr.h"
#include "expr/type.h"
#include <iostream>

namespace CVC4 {

class CVC4_PUBLIC ArrayStoreAll {
  const Type d_type;
  const Expr d_expr;

public:

  ArrayStoreAll(Type type, Expr expr) throw(IllegalArgumentException) :
    d_type(type),
    d_expr(expr) {
    CheckArgument(type.isArray(), type, "array store-all constants can only be created for array types, not `%s'", type.toString().c_str());
    CheckArgument(expr.getType() == ArrayType(type).getConstituentType(), expr, "expr type `%s' does not match constituent type of array type `%s'", expr.getType().toString().c_str(), type.toString().c_str());
  }

  ~ArrayStoreAll() throw() {
  }

  Type getType() const throw() {
    return d_type;
  }
  Expr getExpr() const throw() {
    return d_expr;
  }

  bool operator==(const ArrayStoreAll& asa) const throw() {
    return d_type == asa.d_type && d_expr == asa.d_expr;
  }
  bool operator!=(const ArrayStoreAll& asa) const throw() {
    return !(*this == asa);
  }

  bool operator<(const ArrayStoreAll& asa) const throw() {
    return d_type < asa.d_type ||
           (d_type == asa.d_type && d_expr < asa.d_expr);
  }
  bool operator<=(const ArrayStoreAll& asa) const throw() {
    return d_type < asa.d_type ||
           (d_type == asa.d_type && d_expr <= asa.d_expr);
  }
  bool operator>(const ArrayStoreAll& asa) const throw() {
    return !(*this <= asa);
  }
  bool operator>=(const ArrayStoreAll& asa) const throw() {
    return !(*this < asa);
  }

};/* class ArrayStoreAll */

std::ostream& operator<<(std::ostream& out, const ArrayStoreAll& asa) CVC4_PUBLIC;

/**
 * Hash function for the BitVector constants.
 */
struct CVC4_PUBLIC ArrayStoreAllHashStrategy {
  static inline size_t hash(const ArrayStoreAll& asa) {
    return TypeHashFunction()(asa.getType()) * ExprHashFunction()(asa.getExpr());
  }
};/* struct ArrayStoreAllHashStrategy */

}/* CVC4 namespace */
