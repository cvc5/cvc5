/*********************                                                        */
/*! \file array_store_all.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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
  const ArrayType d_type;
  const Expr d_expr;

public:

  ArrayStoreAll(ArrayType type, Expr expr) throw(IllegalArgumentException) :
    d_type(type),
    d_expr(expr) {

    // this check is stronger than the assertion check in the expr manager that ArrayTypes are actually array types
    // because this check is done in production builds too
    CheckArgument(type.isArray(), type, "array store-all constants can only be created for array types, not `%s'", type.toString().c_str());

    CheckArgument(expr.getType().isSubtypeOf(type.getConstituentType()), expr, "expr type `%s' does not match constituent type of array type `%s'", expr.getType().toString().c_str(), type.toString().c_str());
    CheckArgument(expr.isConst(), expr, "ArrayStoreAll requires a constant expression");
  }

  ~ArrayStoreAll() throw() {
  }

  ArrayType getType() const throw() {
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
 * Hash function for the ArrayStoreAll constants.
 */
struct CVC4_PUBLIC ArrayStoreAllHashFunction {
  inline size_t operator()(const ArrayStoreAll& asa) const {
    return TypeHashFunction()(asa.getType()) * ExprHashFunction()(asa.getExpr());
  }
};/* struct ArrayStoreAllHashFunction */

}/* CVC4 namespace */
