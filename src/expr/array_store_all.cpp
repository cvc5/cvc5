/*********************                                                        */
/*! \file array_store_all.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
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

#include "expr/array_store_all.h"

#include <iostream>

#include "base/cvc4_assert.h"
#include "expr/expr.h"
#include "expr/type.h"

using namespace std;

namespace CVC4 {

ArrayStoreAll::ArrayStoreAll(const ArrayType& type,
                             const Expr& expr) throw(IllegalArgumentException)
    : d_type(NULL), d_expr(NULL) {
  // this check is stronger than the assertion check in the expr manager that
  // ArrayTypes are actually array types
  // because this check is done in production builds too
  PrettyCheckArgument(
      type.isArray(), type,
      "array store-all constants can only be created for array types, not `%s'",
      type.toString().c_str());

  PrettyCheckArgument(
      expr.getType().isComparableTo(type.getConstituentType()), expr,
      "expr type `%s' does not match constituent type of array type `%s'",
      expr.getType().toString().c_str(), type.toString().c_str());

  PrettyCheckArgument(expr.isConst(), expr,
                      "ArrayStoreAll requires a constant expression");

  // Delay allocation until the checks above have been performed. If these fail,
  // the memory for d_type and d_expr should not leak. The alternative is catch,
  // delete and re-throw.
  d_type = new ArrayType(type);
  d_expr = new Expr(expr);
}

ArrayStoreAll::ArrayStoreAll(const ArrayStoreAll& other)
    : d_type(new ArrayType(other.getType())),
      d_expr(new Expr(other.getExpr())) {}

ArrayStoreAll::~ArrayStoreAll() throw() {
  delete d_expr;
  delete d_type;
}

ArrayStoreAll& ArrayStoreAll::operator=(const ArrayStoreAll& other) {
  (*d_type) = other.getType();
  (*d_expr) = other.getExpr();
  return *this;
}

const ArrayType& ArrayStoreAll::getType() const throw() { return *d_type; }

const Expr& ArrayStoreAll::getExpr() const throw() { return *d_expr; }

bool ArrayStoreAll::operator==(const ArrayStoreAll& asa) const throw() {
  return getType() == asa.getType() && getExpr() == asa.getExpr();
}

bool ArrayStoreAll::operator<(const ArrayStoreAll& asa) const throw() {
  return (getType() < asa.getType()) ||
         (getType() == asa.getType() && getExpr() < asa.getExpr());
}

bool ArrayStoreAll::operator<=(const ArrayStoreAll& asa) const throw() {
  return (getType() < asa.getType()) ||
         (getType() == asa.getType() && getExpr() <= asa.getExpr());
}

std::ostream& operator<<(std::ostream& out, const ArrayStoreAll& asa) {
  return out << "__array_store_all__(" << asa.getType() << ", " << asa.getExpr()
             << ')';
}

size_t ArrayStoreAllHashFunction::operator()(const ArrayStoreAll& asa) const {
  return TypeHashFunction()(asa.getType()) * ExprHashFunction()(asa.getExpr());
}

} /* CVC4 namespace */
