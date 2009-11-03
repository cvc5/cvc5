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

  /** Destructor.  Decrements the reference count and, if zero,
   *  collects the ExprValue. */
  ~Expr();

public:
  /** Access to the encapsulated expression.
   *  @return the encapsulated expression. */
  ExprValue* operator->();

  /** Const access to the encapsulated expressoin.
   *  @return the encapsulated expression [const]. */
  const ExprValue* operator->() const;

};/* class Expr */

} /* CVC4 namespace */

#endif /* __CVC4_EXPR_H */
