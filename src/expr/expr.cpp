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
#include "util/Assert.h"

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
  Assert(d_ev != NULL, "Expecting a non-NULL evpression value!");
  d_ev->inc();
}

Expr::Expr(const Expr& e) {
  Assert(e.d_ev != NULL, "Expecting a non-NULL evpression value!");
  d_ev = e.d_ev;
  d_ev->inc();
}

Expr::~Expr() {
  Assert(d_ev != NULL, "Expecting a non-NULL evpression value!");
  d_ev->dec();
}

void Expr::assignExprValue(ExprValue* ev) {
  d_ev = ev;
  d_ev->inc();
}

Expr& Expr::operator=(const Expr& e) {
  Assert(d_ev != NULL, "Expecting a non-NULL evpression value!");
  if(this != &e && d_ev != e.d_ev) {
    d_ev->dec();
    d_ev = e.d_ev;
    d_ev->inc();
  }
  return *this;
}

ExprValue const* Expr::operator->() const {
  Assert(d_ev != NULL, "Expecting a non-NULL evpression value!");
  return d_ev;
}

uint64_t Expr::hash() const {
  Assert(d_ev != NULL, "Expecting a non-NULL evpression value!");
  return d_ev->hash();
}

Expr Expr::eqExpr(const Expr& right) const {
  return ExprManager::currentEM()->mkExpr(EQUAL, *this, right);
}

Expr Expr::notExpr() const {
  return ExprManager::currentEM()->mkExpr(NOT, *this);
}

// FIXME: What does this do and why?
Expr Expr::negate() const { // avoid double-negatives
  return ExprBuilder(*this).negate();
}


Expr Expr::andExpr(const Expr& right) const {
  return ExprManager::currentEM()->mkExpr(AND, *this, right);
}

Expr Expr::orExpr(const Expr& right) const {
  return ExprManager::currentEM()->mkExpr(OR, *this, right);
}

Expr Expr::iteExpr(const Expr& thenpart, const Expr& elsepart) const {
  return ExprManager::currentEM()->mkExpr(ITE, *this, thenpart, elsepart);
}

Expr Expr::iffExpr(const Expr& right) const {
  return ExprManager::currentEM()->mkExpr(IFF, *this, right);
}

Expr Expr::impExpr(const Expr& right) const {
  return ExprManager::currentEM()->mkExpr(IMPLIES, *this, right);
}

Expr Expr::xorExpr(const Expr& right) const {
  return ExprManager::currentEM()->mkExpr(XOR, *this, right);
}

}/* CVC4 namespace */
