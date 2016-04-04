/*********************                                                        */
/*! \file convenience_node_builders.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Convenience node builders.
 **
 ** These are convenience node builders for building AND, OR, PLUS,
 ** and MULT expressions.
 **
 ** \todo These should be moved into theory code (say,
 ** src/theory/booleans/node_builders.h and
 ** src/theory/arith/node_builders.h), but for now they're here
 ** because their design requires CVC4::NodeBuilder to friend them.
 **/

// TODO: add templatized NodeTemplate<ref_count> to all these inlines
// for 'const [T]Node&' arguments?  Technically a lot of time is spent
// in the TNode conversion and copy constructor, but this should be
// optimized into a simple pointer copy (?)
// TODO: double-check this.

#include "cvc4_private.h"

#ifndef __CVC4__CONVENIENCE_NODE_BUILDERS_H
#define __CVC4__CONVENIENCE_NODE_BUILDERS_H

#include "expr/node_builder.h"

namespace CVC4 {

class AndNodeBuilder {
public:
  NodeBuilder<> d_eb;

  inline AndNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    d_eb.collapseTo(kind::AND);
  }

  inline AndNodeBuilder(TNode a, TNode b) : d_eb(kind::AND) {
    d_eb << a << b;
  }

  template <bool rc>
  inline AndNodeBuilder& operator&&(const NodeTemplate<rc>&);

  template <bool rc>
  inline OrNodeBuilder operator||(const NodeTemplate<rc>&);

  inline operator NodeBuilder<>() { return d_eb; }
  inline operator Node() { return d_eb; }

};/* class AndNodeBuilder */

class OrNodeBuilder {
public:
  NodeBuilder<> d_eb;

  inline OrNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    d_eb.collapseTo(kind::OR);
  }

  inline OrNodeBuilder(TNode a, TNode b) : d_eb(kind::OR) {
    d_eb << a << b;
  }

  template <bool rc>
  inline AndNodeBuilder operator&&(const NodeTemplate<rc>&);

  template <bool rc>
  inline OrNodeBuilder& operator||(const NodeTemplate<rc>&);

  inline operator NodeBuilder<>() { return d_eb; }
  inline operator Node() { return d_eb; }

};/* class OrNodeBuilder */

class PlusNodeBuilder {
public:
  NodeBuilder<> d_eb;

  inline PlusNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    d_eb.collapseTo(kind::PLUS);
  }

  inline PlusNodeBuilder(TNode a, TNode b) : d_eb(kind::PLUS) {
    d_eb << a << b;
  }

  template <bool rc>
  inline PlusNodeBuilder& operator+(const NodeTemplate<rc>&);

  template <bool rc>
  inline PlusNodeBuilder& operator-(const NodeTemplate<rc>&);

  template <bool rc>
  inline MultNodeBuilder operator*(const NodeTemplate<rc>&);

  inline operator NodeBuilder<>() { return d_eb; }
  inline operator Node() { return d_eb; }

};/* class PlusNodeBuilder */

class MultNodeBuilder {
public:
  NodeBuilder<> d_eb;

  inline MultNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    d_eb.collapseTo(kind::MULT);
  }

  inline MultNodeBuilder(TNode a, TNode b) : d_eb(kind::MULT) {
    d_eb << a << b;
  }

  template <bool rc>
  inline PlusNodeBuilder operator+(const NodeTemplate<rc>&);

  template <bool rc>
  inline PlusNodeBuilder operator-(const NodeTemplate<rc>&);

  template <bool rc>
  inline MultNodeBuilder& operator*(const NodeTemplate<rc>&);

  inline operator NodeBuilder<>() { return d_eb; }
  inline operator Node() { return d_eb; }

};/* class MultNodeBuilder */

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>& NodeBuilder<nchild_thresh>::operator&=(TNode e) {
  return collapseTo(kind::AND).append(e);
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>& NodeBuilder<nchild_thresh>::operator|=(TNode e) {
  return collapseTo(kind::OR).append(e);
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>& NodeBuilder<nchild_thresh>::operator+=(TNode e) {
  return collapseTo(kind::PLUS).append(e);
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>& NodeBuilder<nchild_thresh>::operator-=(TNode e) {
  return collapseTo(kind::PLUS).
    append(NodeManager::currentNM()->mkNode(kind::UMINUS, e));
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>& NodeBuilder<nchild_thresh>::operator*=(TNode e) {
  return collapseTo(kind::MULT).append(e);
}

template <bool rc>
inline AndNodeBuilder& AndNodeBuilder::operator&&(const NodeTemplate<rc>& n) {
  d_eb.append(n);
  return *this;
}

template <bool rc>
inline OrNodeBuilder AndNodeBuilder::operator||(const NodeTemplate<rc>& n) {
  return OrNodeBuilder(Node(d_eb), n);
}

inline AndNodeBuilder& operator&&(AndNodeBuilder& a,
                                  const AndNodeBuilder& b) {
  return a && Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline AndNodeBuilder& operator&&(AndNodeBuilder& a,
                                  const OrNodeBuilder& b) {
  return a && Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline OrNodeBuilder operator||(AndNodeBuilder& a,
                                const AndNodeBuilder& b) {
  return a || Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline OrNodeBuilder operator||(AndNodeBuilder& a,
                                const OrNodeBuilder& b) {
  return a || Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline AndNodeBuilder OrNodeBuilder::operator&&(const NodeTemplate<rc>& n) {
  return AndNodeBuilder(Node(d_eb), n);
}

template <bool rc>
inline OrNodeBuilder& OrNodeBuilder::operator||(const NodeTemplate<rc>& n) {
  d_eb.append(n);
  return *this;
}

inline AndNodeBuilder operator&&(OrNodeBuilder& a,
                                 const AndNodeBuilder& b) {
  return a && Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline AndNodeBuilder operator&&(OrNodeBuilder& a,
                                 const OrNodeBuilder& b) {
  return a && Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline OrNodeBuilder& operator||(OrNodeBuilder& a,
                                 const AndNodeBuilder& b) {
  return a || Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline OrNodeBuilder& operator||(OrNodeBuilder& a,
                                 const OrNodeBuilder& b) {
  return a || Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline PlusNodeBuilder& PlusNodeBuilder::operator+(const NodeTemplate<rc>& n) {
  d_eb.append(n);
  return *this;
}

template <bool rc>
inline PlusNodeBuilder& PlusNodeBuilder::operator-(const NodeTemplate<rc>& n) {
  d_eb.append(NodeManager::currentNM()->mkNode(kind::UMINUS, n));
  return *this;
}

template <bool rc>
inline MultNodeBuilder PlusNodeBuilder::operator*(const NodeTemplate<rc>& n) {
  return MultNodeBuilder(Node(d_eb), n);
}

inline PlusNodeBuilder& operator+(PlusNodeBuilder& a,
                                  const PlusNodeBuilder& b) {
  return a + Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline PlusNodeBuilder& operator+(PlusNodeBuilder& a,
                                  const MultNodeBuilder& b) {
  return a + Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline PlusNodeBuilder& operator-(PlusNodeBuilder&a,
                                  const PlusNodeBuilder& b) {
  return a - Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline PlusNodeBuilder& operator-(PlusNodeBuilder& a,
                                  const MultNodeBuilder& b) {
  return a - Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline MultNodeBuilder operator*(PlusNodeBuilder& a,
                                 const PlusNodeBuilder& b) {
  return a * Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline MultNodeBuilder operator*(PlusNodeBuilder& a,
                                 const MultNodeBuilder& b) {
  return a * Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline PlusNodeBuilder MultNodeBuilder::operator+(const NodeTemplate<rc>& n) {
  return PlusNodeBuilder(Node(d_eb), n);
}

template <bool rc>
inline PlusNodeBuilder MultNodeBuilder::operator-(const NodeTemplate<rc>& n) {
  return PlusNodeBuilder(Node(d_eb),
                         NodeManager::currentNM()->mkNode(kind::UMINUS, n));
}

template <bool rc>
inline MultNodeBuilder& MultNodeBuilder::operator*(const NodeTemplate<rc>& n) {
  d_eb.append(n);
  return *this;
}

inline PlusNodeBuilder operator+(MultNodeBuilder& a,
                                 const PlusNodeBuilder& b) {
  return a + Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline PlusNodeBuilder operator+(MultNodeBuilder& a,
                                 const MultNodeBuilder& b) {
  return a + Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline PlusNodeBuilder operator-(MultNodeBuilder& a,
                                 const PlusNodeBuilder& b) {
  return a - Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline PlusNodeBuilder operator-(MultNodeBuilder& a,
                                 const MultNodeBuilder& b) {
  return a - Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline MultNodeBuilder& operator*(MultNodeBuilder& a,
                                  const PlusNodeBuilder& b) {
  return a * Node(const_cast<NodeBuilder<>&>(b.d_eb));
}
inline MultNodeBuilder& operator*(MultNodeBuilder& a,
                                  const MultNodeBuilder& b) {
  return a * Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc1, bool rc2>
inline AndNodeBuilder operator&&(const NodeTemplate<rc1>& a,
                                 const NodeTemplate<rc2>& b) {
  return AndNodeBuilder(a, b);
}

template <bool rc1, bool rc2>
inline OrNodeBuilder operator||(const NodeTemplate<rc1>& a,
                                const NodeTemplate<rc2>& b) {
  return OrNodeBuilder(a, b);
}

template <bool rc1, bool rc2>
inline PlusNodeBuilder operator+(const NodeTemplate<rc1>& a,
                                 const NodeTemplate<rc2>& b) {
  return PlusNodeBuilder(a, b);
}

template <bool rc1, bool rc2>
inline PlusNodeBuilder operator-(const NodeTemplate<rc1>& a,
                                 const NodeTemplate<rc2>& b) {
  return PlusNodeBuilder(a, NodeManager::currentNM()->mkNode(kind::UMINUS, b));
}

template <bool rc1, bool rc2>
inline MultNodeBuilder operator*(const NodeTemplate<rc1>& a,
                                 const NodeTemplate<rc2>& b) {
  return MultNodeBuilder(a, b);
}

template <bool rc>
inline AndNodeBuilder operator&&(const NodeTemplate<rc>& a,
                                 const AndNodeBuilder& b) {
  return a && Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline AndNodeBuilder operator&&(const NodeTemplate<rc>& a,
                                 const OrNodeBuilder& b) {
  return a && Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline OrNodeBuilder operator||(const NodeTemplate<rc>& a,
                                const AndNodeBuilder& b) {
  return a || Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline OrNodeBuilder operator||(const NodeTemplate<rc>& a,
                                const OrNodeBuilder& b) {
  return a || Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline PlusNodeBuilder operator+(const NodeTemplate<rc>& a,
                                 const PlusNodeBuilder& b) {
  return a + Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline PlusNodeBuilder operator+(const NodeTemplate<rc>& a,
                                 const MultNodeBuilder& b) {
  return a + Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline PlusNodeBuilder operator-(const NodeTemplate<rc>& a,
                                 const PlusNodeBuilder& b) {
  return a - Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline PlusNodeBuilder operator-(const NodeTemplate<rc>& a,
                                 const MultNodeBuilder& b) {
  return a - Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline MultNodeBuilder operator*(const NodeTemplate<rc>& a,
                                 const PlusNodeBuilder& b) {
  return a * Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline MultNodeBuilder operator*(const NodeTemplate<rc>& a,
                                 const MultNodeBuilder& b) {
  return a * Node(const_cast<NodeBuilder<>&>(b.d_eb));
}

template <bool rc>
inline NodeTemplate<true> operator-(const NodeTemplate<rc>& a) {
  return NodeManager::currentNM()->mkNode(kind::UMINUS, a);
}

}/* CVC4 namespace */

#endif /* __CVC4__CONVENIENCE_NODE_BUILDERS_H */
