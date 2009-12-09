/*********************                                           -*- C++ -*-  */
/** cvc4_expr.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Reference-counted encapsulation of a pointer to an expression.
 **/

#ifndef __CVC4__EXPR_H
#define __CVC4__EXPR_H

#include <vector>
#include <iostream>
#include <stdint.h>

#include "cvc4_config.h"
#include "expr/kind.h"

namespace CVC4 {
  class Expr;
}/* CVC4 namespace */

namespace CVC4 {

inline std::ostream& operator<<(std::ostream&, const Expr&) CVC4_PUBLIC;

class ExprManager;

namespace expr {
  class ExprValue;
}/* CVC4::expr namespace */

using CVC4::expr::ExprValue;

/**
 * Encapsulation of an ExprValue pointer.  The reference count is
 * maintained in the ExprValue.
 */
class CVC4_PUBLIC Expr {

  friend class ExprValue;

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

  friend class ExprBuilder;
  friend class ExprManager;

  /** Access to the encapsulated expression.
   *  @return the encapsulated expression. */
  ExprValue const* operator->() const;

  /**
   * Assigns the expression value and does reference counting. No assumptions are
   * made on the expression, and should only be used if we know what we are
   * doing.
   *
   * @param ev the expression value to assign
   */
  void assignExprValue(ExprValue* ev);

public:

  /** Default constructor, makes a null expression. */
  Expr();

  Expr(const Expr&);

  /** Destructor.  Decrements the reference count and, if zero,
   *  collects the ExprValue. */
  ~Expr();

  bool operator==(const Expr& e) const { return d_ev == e.d_ev; }
  bool operator!=(const Expr& e) const { return d_ev != e.d_ev; }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   */
  inline bool operator<(const Expr& e) const;

  Expr& operator=(const Expr&);

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

  Expr plusExpr(const Expr& right) const;
  Expr uMinusExpr() const;
  Expr multExpr(const Expr& right) const;

  inline Kind getKind() const;

  inline size_t numChildren() const;

  static Expr null() { return s_null; }

  typedef Expr* iterator;
  typedef Expr const* const_iterator;

  inline iterator begin();
  inline iterator end();
  inline const_iterator begin() const;
  inline const_iterator end() const;

  void toString(std::ostream&) const;

  bool isNull() const;

};/* class Expr */

}/* CVC4 namespace */

#include "expr/expr_value.h"

namespace CVC4 {

inline bool Expr::operator<(const Expr& e) const {
  return d_ev->d_id < e.d_ev->d_id;
}

inline std::ostream& operator<<(std::ostream& out, const Expr& e) {
  e.toString(out);
  return out;
}

inline Kind Expr::getKind() const {
  return Kind(d_ev->d_kind);
}

inline void Expr::toString(std::ostream& out) const {
  if(d_ev)
    d_ev->toString(out);
  else out << "null";
}

inline Expr::iterator Expr::begin() {
  return d_ev->begin();
}

inline Expr::iterator Expr::end() {
  return d_ev->end();
}

inline Expr::const_iterator Expr::begin() const {
  return d_ev->begin();
}

inline Expr::const_iterator Expr::end() const {
  return d_ev->end();
}

inline size_t Expr::numChildren() const {
  return d_ev->d_nchildren;
}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_H */
