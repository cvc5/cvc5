/*********************                                           -*- C++ -*-  */
/** expr.h
 ** This file is part of the CVC4 prototype.
 **
 ** Reference-counted encapsulation of a pointer to an expression.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_EXPR_H
#define __CVC4_EXPR_H

#include <vector>
#include <stdint.h>

namespace CVC4 {

class ExprValue;

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

public:
  Expr(const Expr&);

  /** Destructor.  Decrements the reference count and, if zero,
   *  collects the ExprValue. */
  ~Expr();

  Expr& operator=(const Expr&);

  /** Access to the encapsulated expression.
   *  @return the encapsulated expression. */
  ExprValue* operator->();

  /** Const access to the encapsulated expression.
   *  @return the encapsulated expression [const]. */
  const ExprValue* operator->() const;

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

  static Expr null() { return s_null; }
};/* class Expr */

} /* CVC4 namespace */

#endif /* __CVC4_EXPR_H */
