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
  class Node;
}/* CVC4 namespace */

namespace CVC4 {

inline std::ostream& operator<<(std::ostream&, const Node&) CVC4_PUBLIC;

class NodeManager;

namespace expr {
  class ExprValue;
}/* CVC4::expr namespace */

using CVC4::expr::ExprValue;

/**
 * Encapsulation of an ExprValue pointer.  The reference count is
 * maintained in the ExprValue.
 */
class CVC4_PUBLIC Node {

  friend class ExprValue;

  /** A convenient null-valued encapsulated pointer */
  static Node s_null;

  /** The referenced ExprValue */
  ExprValue* d_ev;

  /** This constructor is reserved for use by the Node package; one
   *  must construct an Node using one of the build mechanisms of the
   *  Node package.
   *
   *  Increments the reference count. */
  explicit Node(ExprValue*);

  friend class NodeBuilder;
  friend class NodeManager;

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
  Node();

  Node(const Node&);

  /** Destructor.  Decrements the reference count and, if zero,
   *  collects the ExprValue. */
  ~Node();

  bool operator==(const Node& e) const { return d_ev == e.d_ev; }
  bool operator!=(const Node& e) const { return d_ev != e.d_ev; }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   */
  inline bool operator<(const Node& e) const;

  Node& operator=(const Node&);

  uint64_t hash() const;

  Node eqExpr(const Node& right) const;
  Node notExpr() const;
  Node negate() const; // avoid double-negatives
  Node andExpr(const Node& right) const;
  Node orExpr(const Node& right) const;
  Node iteExpr(const Node& thenpart, const Node& elsepart) const;
  Node iffExpr(const Node& right) const;
  Node impExpr(const Node& right) const;
  Node xorExpr(const Node& right) const;

  Node plusExpr(const Node& right) const;
  Node uMinusExpr() const;
  Node multExpr(const Node& right) const;

  inline Kind getKind() const;

  inline size_t numChildren() const;

  static Node null() { return s_null; }

  typedef Node* iterator;
  typedef Node const* const_iterator;

  inline iterator begin();
  inline iterator end();
  inline const_iterator begin() const;
  inline const_iterator end() const;

  void toString(std::ostream&) const;

  bool isNull() const;

};/* class Node */

}/* CVC4 namespace */

#include "expr/expr_value.h"

namespace CVC4 {

inline bool Node::operator<(const Node& e) const {
  return d_ev->d_id < e.d_ev->d_id;
}

inline std::ostream& operator<<(std::ostream& out, const Node& e) {
  e.toString(out);
  return out;
}

inline Kind Node::getKind() const {
  return Kind(d_ev->d_kind);
}

inline void Node::toString(std::ostream& out) const {
  if(d_ev)
    d_ev->toString(out);
  else out << "null";
}

inline Node::iterator Node::begin() {
  return d_ev->begin();
}

inline Node::iterator Node::end() {
  return d_ev->end();
}

inline Node::const_iterator Node::begin() const {
  return d_ev->begin();
}

inline Node::const_iterator Node::end() const {
  return d_ev->end();
}

inline size_t Node::numChildren() const {
  return d_ev->d_nchildren;
}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_H */
