/*
 * expr.cpp
 *
 *  Created on: Dec 10, 2009
 *      Author: dejan
 */

#include "expr/expr.h"
#include "expr/node.h"
#include "util/Assert.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Expr& e) {
  e.toStream(out);
  return out;
}

Expr::Expr() :
  d_node(new Node()), d_em(NULL) {
}

Expr::Expr(ExprManager* em, Node* node) :
  d_node(node), d_em(em) {
}

Expr::Expr(const Expr& e) :
  d_node(new Node(*e.d_node)), d_em(e.d_em) {
}

ExprManager* Expr::getExprManager() const {
  return d_em;
}

Expr::~Expr() {
  delete d_node;
}

Expr& Expr::operator=(const Expr& e) {
  if(this != &e) {
    delete d_node;
    d_node = new Node(*e.d_node);
    d_em = e.d_em;
  }
  return *this;
}

bool Expr::operator==(const Expr& e) const {
  if(d_em != e.d_em)
    return false;Assert(d_node != NULL, "Unexpected NULL expression pointer!");Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  return *d_node == *e.d_node;
}

bool Expr::operator!=(const Expr& e) const {
  return !(*this == e);
}

bool Expr::operator<(const Expr& e) const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");Assert(e.d_node != NULL, "Unexpected NULL expression pointer!");
  if(d_em != e.d_em)
    return false;
  return *d_node < *e.d_node;
}

uint64_t Expr::hash() const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return (d_node->isNull());
}

Kind Expr::getKind() const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->getKind();
}

size_t Expr::numChildren() const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->numChildren();
}

std::string Expr::toString() const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->toString();
}

bool Expr::isNull() const {
  Assert(d_node != NULL, "Unexpected NULL expression pointer!");
  return d_node->isNull();
}

void Expr::toStream(std::ostream& out) const {
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
  Assert(d_em != NULL, "Don't have an expression manager for this expression!");
  return d_em->mkExpr(NOT, *this);
}

BoolExpr BoolExpr::andExpr(const BoolExpr& e) const {
  Assert(d_em != NULL, "Don't have an expression manager for this expression!");
  Assert(d_em == e.d_em, "Different expression managers!");
  return d_em->mkExpr(AND, *this, e);
}

BoolExpr BoolExpr::orExpr(const BoolExpr& e) const {
  Assert(d_em != NULL, "Don't have an expression manager for this expression!");
  Assert(d_em == e.d_em, "Different expression managers!");
  return d_em->mkExpr(OR, *this, e);
}

BoolExpr BoolExpr::xorExpr(const BoolExpr& e) const {
  Assert(d_em != NULL, "Don't have an expression manager for this expression!");
  Assert(d_em == e.d_em, "Different expression managers!");
  return d_em->mkExpr(XOR, *this, e);
}

BoolExpr BoolExpr::iffExpr(const BoolExpr& e) const {
  Assert(d_em != NULL, "Don't have an expression manager for this expression!");
  Assert(d_em == e.d_em, "Different expression managers!");
  return d_em->mkExpr(IFF, *this, e);
}

BoolExpr BoolExpr::impExpr(const BoolExpr& e) const {
  Assert(d_em != NULL, "Don't have an expression manager for this expression!");
  Assert(d_em == e.d_em, "Different expression managers!");
  return d_em->mkExpr(IMPLIES, *this, e);
}

BoolExpr BoolExpr::iteExpr(const BoolExpr& then_e, const BoolExpr& else_e) const {
  Assert(d_em != NULL, "Don't have an expression manager for this expression!");
  Assert(d_em == then_e.d_em, "Different expression managers!");
  Assert(d_em == else_e.d_em, "Different expression managers!");
  return d_em->mkExpr(ITE, *this, then_e, else_e);
}

Expr BoolExpr::iteExpr(const Expr& then_e, const Expr& else_e) const {
  Assert(d_em != NULL, "Don't have an expression manager for this expression!");
  Assert(d_em == then_e.getExprManager(), "Different expression managers!");
  Assert(d_em == else_e.getExprManager(), "Different expression managers!");
  return d_em->mkExpr(ITE, *this, then_e, else_e);
}

} // End namespace CVC4
