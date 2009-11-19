/*********************                                           -*- C++ -*-  */
/** expr.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Reference-counted encapsulation of a pointer to an expression.
 **/

#ifndef __CVC4_EXPR_H
#define __CVC4_EXPR_H

#include <vector>
#include <stdint.h>
#include "expr/kind.h"

namespace CVC4 {

namespace expr {
  class ExprValue;
}/* CVC4::expr namespace */

using CVC4::expr::ExprValue;

/**
 * Encapsulation of an ExprValue pointer.  The reference count is
 * maintained in the ExprValue.
 */
class Expr {
  /** A convenient null-valued encapsulated pointer */
  static Expr s_null;

  /** The referenced ExprValue */
  ExprValue* d_ev;

  /** This constructor is reserved for use by the Expr package; one
   *  must construct an Expr using one of the build mechanisms of the
   *  Expr package.
   *
   *  Increments the reference count. */
  explicit Expr(ExprValue*);

  typedef Expr* iterator;
  typedef Expr const* const_iterator;

  friend class ExprBuilder;

public:
  Expr(const Expr&);

  /** Destructor.  Decrements the reference count and, if zero,
   *  collects the ExprValue. */
  ~Expr();

  Expr& operator=(const Expr&);

  /** Access to the encapsulated expression.
   *  @return the encapsulated expression. */
  ExprValue* operator->() const;

  uint64_t hash() const;

  Expr eqExpr(const Expr& right) const;
  Expr notExpr() const;
  Expr negate() const; // avoid double-negatives
  Expr andExpr(const Expr& right) const;
  Expr orExpr(const Expr& right) const;
  Expr iteExpr(const Expr& thenpart, const Expr& elsepart) const;
  Expr iffExpr(const Expr& right) const;
  Expr impExpr(const Expr& right) const;
  Expr xorExpr(const Expr& right) const;
  Expr skolemExpr(int i) const;
  Expr substExpr(const std::vector<Expr>& oldTerms,
                 const std::vector<Expr>& newTerms) const;

  inline Kind getKind() const;

  static Expr null() { return s_null; }

};/* class Expr */

}/* CVC4 namespace */

#include "expr/expr_value.h"

namespace CVC4 {

inline Kind Expr::getKind() const {
  return Kind(d_ev->d_kind);
}

}/* CVC4 namespace */

#endif /* __CVC4_EXPR_H */
