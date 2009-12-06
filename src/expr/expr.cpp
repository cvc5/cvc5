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

#include "expr/expr.h"
#include "expr_value.h"
#include "expr_builder.h"

using namespace CVC4::expr;

namespace CVC4 {

ExprValue ExprValue::s_null;

Expr Expr::s_null(&ExprValue::s_null);

bool Expr::isNull() const {
  return d_ev == &ExprValue::s_null;
}

Expr::Expr() :
  d_ev(&ExprValue::s_null) {
  // No refcount needed
}

Expr::Expr(ExprValue* ev)
  : d_ev(ev) {
  if(d_ev != 0)
    d_ev->inc();
}

Expr::Expr(const Expr& e) {
  if((d_ev = e.d_ev) && d_ev != 0)
    d_ev->inc();
}

Expr::~Expr() {
  if(d_ev)
    d_ev->dec();
}

Expr& Expr::operator=(const Expr& e) {
  if(d_ev)
    d_ev->dec();
  if((d_ev = e.d_ev))
    d_ev->inc();
  return *this;
}

ExprValue* Expr::operator->() const {
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

}/* CVC4 namespace */
