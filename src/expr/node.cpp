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

#include "expr/node.h"
#include "expr/expr_value.h"
#include "expr/node_builder.h"
#include "util/Assert.h"

using namespace CVC4::expr;

namespace CVC4 {

ExprValue ExprValue::s_null;

Node Node::s_null(&ExprValue::s_null);

bool Node::isNull() const {
  return d_ev == &ExprValue::s_null;
}

Node::Node() :
  d_ev(&ExprValue::s_null) {
  // No refcount needed
}

Node::Node(ExprValue* ev)
  : d_ev(ev) {
  Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
  d_ev->inc();
}

Node::Node(const Node& e) {
  Assert(e.d_ev != NULL, "Expecting a non-NULL expression value!");
  d_ev = e.d_ev;
  d_ev->inc();
}

Node::~Node() {
  Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
  d_ev->dec();
}

void Node::assignExprValue(ExprValue* ev) {
  d_ev = ev;
  d_ev->inc();
}

Node& Node::operator=(const Node& e) {
  Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
  if(this != &e && d_ev != e.d_ev) {
    d_ev->dec();
    d_ev = e.d_ev;
    d_ev->inc();
  }
  return *this;
}

ExprValue const* Node::operator->() const {
  Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
  return d_ev;
}

uint64_t Node::hash() const {
  Assert(d_ev != NULL, "Expecting a non-NULL expression value!");
  return d_ev->hash();
}

Node Node::eqExpr(const Node& right) const {
  return NodeManager::currentEM()->mkExpr(EQUAL, *this, right);
}

Node Node::notExpr() const {
  return NodeManager::currentEM()->mkExpr(NOT, *this);
}

// FIXME: What does this do and why?
Node Node::negate() const { // avoid double-negatives
  return NodeBuilder(*this).negate();
}


Node Node::andExpr(const Node& right) const {
  return NodeManager::currentEM()->mkExpr(AND, *this, right);
}

Node Node::orExpr(const Node& right) const {
  return NodeManager::currentEM()->mkExpr(OR, *this, right);
}

Node Node::iteExpr(const Node& thenpart, const Node& elsepart) const {
  return NodeManager::currentEM()->mkExpr(ITE, *this, thenpart, elsepart);
}

Node Node::iffExpr(const Node& right) const {
  return NodeManager::currentEM()->mkExpr(IFF, *this, right);
}

Node Node::impExpr(const Node& right) const {
  return NodeManager::currentEM()->mkExpr(IMPLIES, *this, right);
}

Node Node::xorExpr(const Node& right) const {
  return NodeManager::currentEM()->mkExpr(XOR, *this, right);
}

}/* CVC4 namespace */
