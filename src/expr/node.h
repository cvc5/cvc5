/*********************                                           -*- C++ -*-  */
/** node.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "expr/node_value.h"

#ifndef __CVC4__NODE_H
#define __CVC4__NODE_H

#include <vector>
#include <string>
#include <iostream>
#include <stdint.h>

#include "cvc4_config.h"
#include "expr/kind.h"
#include "util/Assert.h"

namespace CVC4 {
  class Node;
}/* CVC4 namespace */

namespace CVC4 {

inline std::ostream& operator<<(std::ostream&, const Node&);

class NodeManager;

namespace expr {
  class NodeValue;
}/* CVC4::expr namespace */

using CVC4::expr::NodeValue;

/**
 * Encapsulation of an NodeValue pointer.  The reference count is
 * maintained in the NodeValue.
 */
class Node {

  friend class NodeValue;

  /** A convenient null-valued encapsulated pointer */
  static Node s_null;

  /** The referenced NodeValue */
  NodeValue* d_ev;

  /** This constructor is reserved for use by the Node package; one
   *  must construct an Node using one of the build mechanisms of the
   *  Node package.
   *
   *  Increments the reference count.
   *
   *  FIXME: there's a type-system escape here to cast away the const,
   *  since the refcount needs to be updated.  But conceptually Nodes
   *  don't change their arguments, and it's nice to have
   *  const_iterators over them.  See notes in .cpp file for
   *  details. */
  // this really does needs to be explicit to avoid hard to track
  // errors with Nodes implicitly wrapping NodeValues
  explicit Node(const NodeValue*);

  template <unsigned> friend class NodeBuilder;
  friend class NodeManager;

  /**
   * Assigns the expression value and does reference counting. No assumptions
   * are made on the expression, and should only be used if we know what we are
   * doing.
   *
   * @param ev the expression value to assign
   */
  void assignNodeValue(NodeValue* ev);

  typedef NodeValue::ev_iterator ev_iterator;
  typedef NodeValue::const_ev_iterator const_ev_iterator;

  inline ev_iterator ev_begin();
  inline ev_iterator ev_end();
  inline const_ev_iterator ev_begin() const;
  inline const_ev_iterator ev_end() const;

public:

  /** Default constructor, makes a null expression. */
  Node();

  Node(const Node&);

  /** Destructor.  Decrements the reference count and, if zero,
   *  collects the NodeValue. */
  ~Node();

  bool operator==(const Node& e) const { return d_ev == e.d_ev; }
  bool operator!=(const Node& e) const { return d_ev != e.d_ev; }

  Node operator[](int i) const {
    Assert(i >= 0 && i < d_ev->d_nchildren);
    return Node(d_ev->d_children[i]);
  }

  /**
   * We compare by expression ids so, keeping things deterministic and having
   * that subexpressions have to be smaller than the enclosing expressions.
   */
  inline bool operator<(const Node& e) const;

  Node& operator=(const Node&);

  uint64_t hash() const;
  uint64_t getId() const { return d_ev->getId(); }

  Node eqExpr(const Node& right) const;
  Node notExpr() const;
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

  inline size_t getNumChildren() const;

  static Node null();

  typedef NodeValue::node_iterator iterator;
  typedef NodeValue::node_iterator const_iterator;

  inline iterator begin();
  inline iterator end();
  inline const_iterator begin() const;
  inline const_iterator end() const;

  inline std::string toString() const;
  inline void toStream(std::ostream&) const;

  bool isNull() const;

};/* class Node */

}/* CVC4 namespace */

#include "expr/node_value.h"

namespace CVC4 {

inline bool Node::operator<(const Node& e) const {
  return d_ev->d_id < e.d_ev->d_id;
}

inline std::ostream& operator<<(std::ostream& out, const Node& e) {
  e.toStream(out);
  return out;
}

inline Kind Node::getKind() const {
  return Kind(d_ev->d_kind);
}

inline std::string Node::toString() const {
  return d_ev->toString();
}

inline void Node::toStream(std::ostream& out) const {
  d_ev->toStream(out);
}

inline Node::ev_iterator Node::ev_begin() {
  return d_ev->ev_begin();
}

inline Node::ev_iterator Node::ev_end() {
  return d_ev->ev_end();
}

inline Node::const_ev_iterator Node::ev_begin() const {
  return d_ev->ev_begin();
}

inline Node::const_ev_iterator Node::ev_end() const {
  return d_ev->ev_end();
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

inline size_t Node::getNumChildren() const {
  return d_ev->d_nchildren;
}

}/* CVC4 namespace */

#endif /* __CVC4__NODE_H */
