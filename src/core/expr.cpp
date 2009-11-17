/*********************                                           -*- C++ -*-  */
/** expr.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Reference-counted encapsulation of a pointer to an expression.
 **/

#include "cvc4_expr.h"
#include "core/expr_value.h"
#include "core/expr_builder.h"

namespace CVC4 {

Expr Expr::s_null(0);

Expr::Expr(ExprValue* ev)
  : d_ev(ev) {
  // FIXME: thread-safety
  ++d_ev->d_rc;
}

Expr::Expr(const Expr& e) {
  // FIXME: thread-safety
  if((d_ev = e.d_ev))
    ++d_ev->d_rc;
}

Expr::~Expr() {
  // FIXME: thread-safety
  --d_ev->d_rc;
}

Expr& Expr::operator=(const Expr& e) {
  // FIXME: thread-safety
  if(d_ev)
    --d_ev->d_rc;
  if((d_ev = e.d_ev))
    ++d_ev->d_rc;
  return *this;
}

ExprValue* Expr::operator->() {
  return d_ev;
}

const ExprValue* Expr::operator->() const {
  return d_ev;
}

uint64_t Expr::hash() const {
  return d_ev->hash();
}

Expr Expr::eqExpr(const Expr& right) const {
  return ExprBuilder(*this).eqExpr(right);
}

Expr Expr::notExpr() const {
  return ExprBuilder(*this).notExpr();
}

Expr Expr::negate() const { // avoid double-negatives
  return ExprBuilder(*this).negate();
}

Expr Expr::andExpr(const Expr& right) const {
  return ExprBuilder(*this).andExpr(right);
}

Expr Expr::orExpr(const Expr& right) const {
  return ExprBuilder(*this).orExpr(right);
}

Expr Expr::iteExpr(const Expr& thenpart, const Expr& elsepart) const {
  return ExprBuilder(*this).iteExpr(thenpart, elsepart);
}

Expr Expr::iffExpr(const Expr& right) const {
  return ExprBuilder(*this).iffExpr(right);
}

Expr Expr::impExpr(const Expr& right) const {
  return ExprBuilder(*this).impExpr(right);
}

Expr Expr::xorExpr(const Expr& right) const {
  return ExprBuilder(*this).xorExpr(right);
}

Expr Expr::skolemExpr(int i) const {
  return ExprBuilder(*this).skolemExpr(i);
}

Expr Expr::substExpr(const std::vector<Expr>& oldTerms,
                     const std::vector<Expr>& newTerms) const {
  return ExprBuilder(*this).substExpr(oldTerms, newTerms);
}

} /* CVC4 namespace */
