/*********************                                                        */
/** expr_template.cpp
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Public-facing expression interface, implementation.
 **/

#include "expr/expr.h"
#include "expr/node.h"
#include "util/Assert.h"

#include "util/output.h"

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 29 "${template}"

using namespace CVC4::kind;

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Expr& e) {
  e.toStream(out);
  return out;
}

Expr::Expr() :
  d_node(new Node),
  d_exprManager(NULL) {
}

Expr::Expr(ExprManager* em, Node* node) :
  d_node(node),
  d_exprManager(em) {
}

Expr::Expr(const Expr& e) :
  d_node(new Node(*e.d_node)),
  d_exprManager(e.d_exprManager) {
}

Expr::Expr(uintptr_t n) :
  d_node(new Node),
  d_exprManager(NULL) {

  AlwaysAssert(n == 0);
}

Expr::~Expr() {
  ExprManagerScope ems(*this);
  delete d_node;
}

ExprManager* Expr::getExprManager() const {
  return d_exprManager;
}

Expr& Expr::operator=(const Expr& e) {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");

  ExprManagerScope ems(*this);
  *d_node = *e.d_node;
  d_exprManager = e.d_exprManager;

  return *this;
}

/* This should only ever be assigning NULL to a null Expr! */
Expr& Expr::operator=(uintptr_t n) {
  AlwaysAssert(n == 0);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");

  if(EXPECT_FALSE( !isNull() )) {
    *d_node = Node::null();
  }
  return *this;
}

bool Expr::operator==(const Expr& e) const {
  if(d_exprManager != e.d_exprManager) {
    return false;
  }
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  return *d_node == *e.d_node;
}

bool Expr::operator!=(const Expr& e) const {
  return !(*this == e);
}

bool Expr::operator<(const Expr& e) const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  if(isNull() && !e.isNull()) {
    return true;
  }
  ExprManagerScope ems(*this);
  return *d_node < *e.d_node;
}

Kind Expr::getKind() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getKind();
}

size_t Expr::getNumChildren() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getNumChildren();
}

bool Expr::hasOperator() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->hasOperator();
}

Expr Expr::getOperator() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  CheckArgument(d_node->hasOperator(),
                "Expr::getOperator() called on an Expr with no operator");
  return Expr(d_exprManager, new Node(d_node->getOperator()));
}

Type* Expr::getType() const {
  ExprManagerScope ems(*this);
  return d_node->getType();
}

std::string Expr::toString() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->toString();
}

bool Expr::isNull() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->isNull();
}

Expr::operator bool() const {
  return !isNull();
}

bool Expr::isConst() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->isConst();
}

bool Expr::isAtomic() const {
  ExprManagerScope ems(*this);
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->isAtomic();
}

void Expr::toStream(std::ostream& out) const {
  ExprManagerScope ems(*this);
  d_node->toStream(out);
}

Node Expr::getNode() const {
  return *d_node;
}

BoolExpr::BoolExpr() {
}

BoolExpr::BoolExpr(const Expr& e) :
  Expr(e) {
}

BoolExpr BoolExpr::notExpr() const {
  Assert(d_exprManager != NULL, "Don't have an expression manager for this expression!");
  return d_exprManager->mkExpr(NOT, *this);
}

BoolExpr BoolExpr::andExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL, "Don't have an expression manager for this expression!");
  Assert(d_exprManager == e.d_exprManager, "Different expression managers!");
  return d_exprManager->mkExpr(AND, *this, e);
}

BoolExpr BoolExpr::orExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL, "Don't have an expression manager for this expression!");
  Assert(d_exprManager == e.d_exprManager, "Different expression managers!");
  return d_exprManager->mkExpr(OR, *this, e);
}

BoolExpr BoolExpr::xorExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL, "Don't have an expression manager for this expression!");
  Assert(d_exprManager == e.d_exprManager, "Different expression managers!");
  return d_exprManager->mkExpr(XOR, *this, e);
}

BoolExpr BoolExpr::iffExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL, "Don't have an expression manager for this expression!");
  Assert(d_exprManager == e.d_exprManager, "Different expression managers!");
  return d_exprManager->mkExpr(IFF, *this, e);
}

BoolExpr BoolExpr::impExpr(const BoolExpr& e) const {
  Assert(d_exprManager != NULL, "Don't have an expression manager for this expression!");
  Assert(d_exprManager == e.d_exprManager, "Different expression managers!");
  return d_exprManager->mkExpr(IMPLIES, *this, e);
}

BoolExpr BoolExpr::iteExpr(const BoolExpr& then_e, const BoolExpr& else_e) const {
  Assert(d_exprManager != NULL, "Don't have an expression manager for this expression!");
  Assert(d_exprManager == then_e.d_exprManager, "Different expression managers!");
  Assert(d_exprManager == else_e.d_exprManager, "Different expression managers!");
  return d_exprManager->mkExpr(ITE, *this, then_e, else_e);
}

Expr BoolExpr::iteExpr(const Expr& then_e, const Expr& else_e) const {
  Assert(d_exprManager != NULL, "Don't have an expression manager for this expression!");
  Assert(d_exprManager == then_e.getExprManager(), "Different expression managers!");
  Assert(d_exprManager == else_e.getExprManager(), "Different expression managers!");
  return d_exprManager->mkExpr(ITE, *this, then_e, else_e);
}

void Expr::printAst(std::ostream & o, int indent) const {
  ExprManagerScope ems(*this);
  getNode().printAst(o, indent);
}

void Expr::debugPrint() {
#ifndef CVC4_MUZZLE
  printAst(Warning());
  Warning().flush();
#endif /* ! CVC4_MUZZLE */
}

${getConst_implementations}

}/* CVC4 namespace */
