/*********************                                                        */
/** expr.cpp
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
 ** [[ Add file-specific comments here ]]
 **/

#include "expr/expr.h"
#include "expr/node.h"
#include "util/Assert.h"

#include "util/output.h"

using namespace CVC4::kind;

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Expr& e) {
  e.toStream(out);
  return out;
}

Expr::Expr() :
  d_node(new Node()), d_exprManager(NULL) {
}

Expr::Expr(ExprManager* em, Node* node) :
  d_node(node), d_exprManager(em) {
}

Expr::Expr(const Expr& e) :
  d_node(new Node(*e.d_node)), d_exprManager(e.d_exprManager) {
}

ExprManager* Expr::getExprManager() const {
  return d_exprManager;
}

Expr::~Expr() {
  ExprManagerScope ems(*this);
  delete d_node;
}

Expr& Expr::operator=(const Expr& e) {
  if(this != &e) {
    ExprManagerScope ems(*this);
    delete d_node;
    d_node = new Node(*e.d_node);
    d_exprManager = e.d_exprManager;
  }
  return *this;
}

bool Expr::operator==(const Expr& e) const {
  if(d_exprManager != e.d_exprManager) {
    return false;
  }
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
  if(d_exprManager != e.d_exprManager) {
    return false;
  }
  return *d_node < *e.d_node;
}

Kind Expr::getKind() const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getKind();
}

size_t Expr::getNumChildren() const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getNumChildren();
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
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->isNull();
}

Expr::operator bool() const {
  return !isNull();
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
  getNode().printAst(o, indent);
}

void Expr::debugPrint() {
#ifndef CVC4_MUZZLE
  printAst(Warning());
  Warning().flush();
#endif /* ! CVC4_MUZZLE */
}


} // End namespace CVC4
