/*********************                                                        */
/** node_builder.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A builder interface for nodes.
 **/

#include "cvc4_private.h"

/* strong dependency; make sure node is included first */
#include "node.h"

#ifndef __CVC4__NODE_BUILDER_H
#define __CVC4__NODE_BUILDER_H

#include <vector>
#include <cstdlib>
#include <stdint.h>

namespace CVC4 {
  static const unsigned default_nchild_thresh = 10;

  template <unsigned nchild_thresh = default_nchild_thresh>
  class NodeBuilder;

  class NodeManager;
}/* CVC4 namespace */

#include "expr/kind.h"
#include "util/Assert.h"
#include "expr/node_value.h"
#include "util/output.h"

namespace CVC4 {

template <unsigned nchild_thresh>
inline std::ostream& operator<<(std::ostream&, const NodeBuilder<nchild_thresh>&);

class AndNodeBuilder;
class OrNodeBuilder;
class PlusNodeBuilder;
class MultNodeBuilder;

template <unsigned nchild_thresh>
class NodeBuilder {

  unsigned d_size;

  uint64_t d_hash;

  NodeManager* d_nm;

  // initially false, when you extract the Node this is set and you can't
  // extract another
  bool d_used;

  expr::NodeValue* d_nv;
  expr::NodeValue d_inlineNv;
  expr::NodeValue *d_childrenStorage[nchild_thresh];

  bool nvIsAllocated() const {
    return d_nv->d_nchildren > nchild_thresh;
  }

  template <unsigned N>
  bool nvIsAllocated(const NodeBuilder<N>& nb) const {
    return nb.d_nv->d_nchildren > N;
  }

  bool evNeedsToBeAllocated() const {
    return d_nv->d_nchildren == d_size;
  }

  // realloc in the default way
  void realloc();

  // realloc to a specific size
  void realloc(size_t toSize, bool copy = true);

  void allocateEvIfNecessaryForAppend() {
    if(EXPECT_FALSE( evNeedsToBeAllocated() )) {
      realloc();
    }
  }

  // dealloc: only call this with d_used == false and nvIsAllocated()
  inline void dealloc();

  void crop() {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    if(EXPECT_FALSE( nvIsAllocated() ) && EXPECT_TRUE( d_size > d_nv->d_nchildren )) {
      d_nv = (expr::NodeValue*)
        std::realloc(d_nv, sizeof(expr::NodeValue) +
                     ( sizeof(expr::NodeValue*) * (d_size = d_nv->d_nchildren) ));
      if(d_nv == NULL) {
        throw std::bad_alloc();
      }
    }
  }

  NodeBuilder& collapseTo(Kind k) {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    AssertArgument(k != kind::UNDEFINED_KIND && k != kind::NULL_EXPR,
                   k, "illegal collapsing kind");

    if(getKind() != k) {
      Node n = *this;
      clear();
      d_nv->d_kind = k;
      append(n);
    }
    return *this;
  }

public:

  inline NodeBuilder();
  inline NodeBuilder(Kind k);
  inline NodeBuilder(const NodeBuilder<nchild_thresh>& nb);
  template <unsigned N> inline NodeBuilder(const NodeBuilder<N>& nb);
  inline NodeBuilder(NodeManager* nm);
  inline NodeBuilder(NodeManager* nm, Kind k);
  inline ~NodeBuilder();

  typedef expr::NodeValue::iterator<true> iterator;
  typedef expr::NodeValue::iterator<true> const_iterator;

  const_iterator begin() const {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    return d_nv->begin<true>();
  }

  const_iterator end() const {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    return d_nv->end<true>();
  }

  Kind getKind() const {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    return d_nv->getKind();
  }

  unsigned getNumChildren() const {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    return d_nv->getNumChildren();
  }

  Node operator[](int i) const {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    Assert(i >= 0 && i < d_nv->getNumChildren());
    return Node(d_nv->d_children[i]);
  }

  /**
   * "Reset" this node builder (optionally setting a new kind for it),
   * using the same memory as before.  This should leave the
   * NodeBuilder<> in the state it was after initial construction.
   */
  void clear(Kind k = kind::UNDEFINED_KIND);

  // "Stream" expression constructor syntax

  NodeBuilder& operator<<(const Kind& k) {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    Assert(d_nv->getKind() == kind::UNDEFINED_KIND);
    d_nv->d_kind = k;
    return *this;
  }

  NodeBuilder& operator<<(TNode n) {
    // FIXME: collapse if ! UNDEFINED_KIND
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    return append(n);
  }

  // For pushing sequences of children
  NodeBuilder& append(const std::vector<Node>& children) {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    return append(children.begin(), children.end());
  }

  NodeBuilder& append(TNode n) {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    Debug("node") << "append: " << this << " " << n << "[" << n.d_nv << "]" << std::endl;
    allocateEvIfNecessaryForAppend();
    expr::NodeValue* ev = n.d_nv;
    ev->inc();
    d_nv->d_children[d_nv->d_nchildren++] = ev;
    return *this;
  }

  template <class Iterator>
  NodeBuilder& append(const Iterator& begin, const Iterator& end) {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    for(Iterator i = begin; i != end; ++i) {
      append(*i);
    }
    return *this;
  }

  operator Node();
  operator Node() const;

  inline void toStream(std::ostream& out) const {
    Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
    d_nv->toStream(out);
  }

  NodeBuilder& operator&=(TNode);
  NodeBuilder& operator|=(TNode);
  NodeBuilder& operator+=(TNode);
  NodeBuilder& operator-=(TNode);
  NodeBuilder& operator*=(TNode);

  friend class AndNodeBuilder;
  friend class OrNodeBuilder;
  friend class PlusNodeBuilder;
  friend class MultNodeBuilder;

  // Yet 1 more example of how terrifying C++ is as a language
  // This is needed for copy constructors of different sizes to access private fields
  template <unsigned N>
  friend class NodeBuilder;

};/* class NodeBuilder */

// TODO: add templatized NodeTemplate<ref_count> to all above and
// below inlines for 'const [T]Node&' arguments?  Technically a lot of
// time is spent in the TNode conversion and copy constructor, but
// this should be optimized into a simple pointer copy (?)
// TODO: double-check this.

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
  return collapseTo(kind::PLUS).append(NodeManager::currentNM()->mkNode(kind::UMINUS, e));
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

inline AndNodeBuilder& operator&&(AndNodeBuilder& a, const AndNodeBuilder& b) {
  return a && Node(b.d_eb);
}
inline AndNodeBuilder& operator&&(AndNodeBuilder& a, const OrNodeBuilder& b) {
  return a && Node(b.d_eb);
}
inline OrNodeBuilder operator||(AndNodeBuilder& a, const AndNodeBuilder& b) {
  return a || Node(b.d_eb);
}
inline OrNodeBuilder operator||(AndNodeBuilder& a, const OrNodeBuilder& b) {
  return a || Node(b.d_eb);
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

inline AndNodeBuilder operator&&(OrNodeBuilder& a, const AndNodeBuilder& b) {
  return a && Node(b.d_eb);
}
inline AndNodeBuilder operator&&(OrNodeBuilder& a, const OrNodeBuilder& b) {
  return a && Node(b.d_eb);
}
inline OrNodeBuilder& operator||(OrNodeBuilder& a, const AndNodeBuilder& b) {
  return a || Node(b.d_eb);
}
inline OrNodeBuilder& operator||(OrNodeBuilder& a, const OrNodeBuilder& b) {
  return a || Node(b.d_eb);
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

inline PlusNodeBuilder& operator+(PlusNodeBuilder& a, const PlusNodeBuilder& b) {
  return a + Node(b.d_eb);
}
inline PlusNodeBuilder& operator+(PlusNodeBuilder& a, const MultNodeBuilder& b) {
  return a + Node(b.d_eb);
}
inline PlusNodeBuilder& operator-(PlusNodeBuilder&a, const PlusNodeBuilder& b) {
  return a - Node(b.d_eb);
}
inline PlusNodeBuilder& operator-(PlusNodeBuilder& a, const MultNodeBuilder& b) {
  return a - Node(b.d_eb);
}
inline MultNodeBuilder operator*(PlusNodeBuilder& a, const PlusNodeBuilder& b) {
  return a * Node(b.d_eb);
}
inline MultNodeBuilder operator*(PlusNodeBuilder& a, const MultNodeBuilder& b) {
  return a * Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder MultNodeBuilder::operator+(const NodeTemplate<rc>& n) {
  return PlusNodeBuilder(Node(d_eb), n);
}

template <bool rc>
inline PlusNodeBuilder MultNodeBuilder::operator-(const NodeTemplate<rc>& n) {
  return PlusNodeBuilder(Node(d_eb), NodeManager::currentNM()->mkNode(kind::UMINUS, n));
}

template <bool rc>
inline MultNodeBuilder& MultNodeBuilder::operator*(const NodeTemplate<rc>& n) {
  d_eb.append(n);
  return *this;
}

inline PlusNodeBuilder operator+(MultNodeBuilder& a, const PlusNodeBuilder& b) {
  return a + Node(b.d_eb);
}
inline PlusNodeBuilder operator+(MultNodeBuilder& a, const MultNodeBuilder& b) {
  return a + Node(b.d_eb);
}
inline PlusNodeBuilder operator-(MultNodeBuilder& a, const PlusNodeBuilder& b) {
  return a - Node(b.d_eb);
}
inline PlusNodeBuilder operator-(MultNodeBuilder& a, const MultNodeBuilder& b) {
  return a - Node(b.d_eb);
}
inline MultNodeBuilder& operator*(MultNodeBuilder& a, const PlusNodeBuilder& b) {
  return a * Node(b.d_eb);
}
inline MultNodeBuilder& operator*(MultNodeBuilder& a, const MultNodeBuilder& b) {
  return a * Node(b.d_eb);
}

template <bool rc1, bool rc2>
inline AndNodeBuilder operator&&(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return AndNodeBuilder(a, b);
}

template <bool rc1, bool rc2>
inline OrNodeBuilder operator||(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return OrNodeBuilder(a, b);
}

template <bool rc1, bool rc2>
inline PlusNodeBuilder operator+(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return PlusNodeBuilder(a, b);
}

template <bool rc1, bool rc2>
inline PlusNodeBuilder operator-(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return PlusNodeBuilder(a, NodeManager::currentNM()->mkNode(kind::UMINUS, b));
}

template <bool rc1, bool rc2>
inline MultNodeBuilder operator*(const NodeTemplate<rc1>& a, const NodeTemplate<rc2>& b) {
  return MultNodeBuilder(a, b);
}

template <bool rc>
inline AndNodeBuilder operator&&(const NodeTemplate<rc>& a, const AndNodeBuilder& b) {
  return a && Node(b.d_eb);
}

template <bool rc>
inline AndNodeBuilder operator&&(const NodeTemplate<rc>& a, const OrNodeBuilder& b) {
  return a && Node(b.d_eb);
}

template <bool rc>
inline OrNodeBuilder operator||(const NodeTemplate<rc>& a, const AndNodeBuilder& b) {
  return a || Node(b.d_eb);
}

template <bool rc>
inline OrNodeBuilder operator||(const NodeTemplate<rc>& a, const OrNodeBuilder& b) {
  return a || Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder operator+(const NodeTemplate<rc>& a, const PlusNodeBuilder& b) {
  return a + Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder operator+(const NodeTemplate<rc>& a, const MultNodeBuilder& b) {
  return a + Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder operator-(const NodeTemplate<rc>& a, const PlusNodeBuilder& b) {
  return a - Node(b.d_eb);
}

template <bool rc>
inline PlusNodeBuilder operator-(const NodeTemplate<rc>& a, const MultNodeBuilder& b) {
  return a - Node(b.d_eb);
}

template <bool rc>
inline MultNodeBuilder operator*(const NodeTemplate<rc>& a, const PlusNodeBuilder& b) {
  return a * Node(b.d_eb);
}

template <bool rc>
inline MultNodeBuilder operator*(const NodeTemplate<rc>& a, const MultNodeBuilder& b) {
  return a * Node(b.d_eb);
}

template <bool rc>
inline NodeTemplate<true> operator-(const NodeTemplate<rc>& a) {
  return NodeManager::currentNM()->mkNode(kind::UMINUS, a);
}

}/* CVC4 namespace */

#include "expr/node.h"
#include "expr/node_manager.h"

// template implementations

namespace CVC4 {

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder() :
  d_size(nchild_thresh),
  d_hash(0),
  d_nm(NodeManager::currentNM()),
  d_used(false),
  d_nv(&d_inlineNv),
  d_inlineNv(0),
  d_childrenStorage() {}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder(Kind k) :
  d_size(nchild_thresh),
  d_hash(0),
  d_nm(NodeManager::currentNM()),
  d_used(false),
  d_nv(&d_inlineNv),
  d_inlineNv(0),
  d_childrenStorage() {

  d_inlineNv.d_kind = k;
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder(const NodeBuilder<nchild_thresh>& nb) :
  d_size(nchild_thresh),
  d_hash(0),
  d_nm(nb.d_nm),
  d_used(nb.d_used),
  d_nv(&d_inlineNv),
  d_inlineNv(0),
  d_childrenStorage() {

  if(nvIsAllocated(nb)) {
    realloc(nb.d_size, false);
    std::copy(nb.d_nv->nv_begin(), nb.d_nv->nv_end(), d_nv->nv_begin());
  } else {
    std::copy(nb.d_nv->nv_begin(), nb.d_nv->nv_end(), d_inlineNv.nv_begin());
  }
  d_nv->d_kind = nb.d_nv->d_kind;
  d_nv->d_nchildren = nb.d_nv->d_nchildren;
  for(expr::NodeValue::nv_iterator i = d_nv->nv_begin();
      i != d_nv->nv_end();
      ++i) {
    (*i)->inc();
  }
}

template <unsigned nchild_thresh>
template <unsigned N>
inline NodeBuilder<nchild_thresh>::NodeBuilder(const NodeBuilder<N>& nb) :
  d_size(nchild_thresh),
  d_hash(0),
  d_nm(NodeManager::currentNM()),
  d_used(nb.d_used),
  d_nv(&d_inlineNv),
  d_inlineNv(0),
  d_childrenStorage() {

  if(nb.d_nv->d_nchildren > nchild_thresh) {
    realloc(nb.d_size, false);
    std::copy(nb.d_nv->nv_begin(), nb.d_nv->nv_end(), d_nv->nv_begin());
  } else {
    std::copy(nb.d_nv->nv_begin(), nb.d_nv->nv_end(), d_inlineNv.nv_begin());
  }
  d_nv->d_kind = nb.d_nv->d_kind;
  d_nv->d_nchildren = nb.d_nv->d_nchildren;
  for(expr::NodeValue::nv_iterator i = d_nv->nv_begin();
      i != d_nv->nv_end();
      ++i) {
    (*i)->inc();
  }
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder(NodeManager* nm) :
  d_size(nchild_thresh),
  d_hash(0),
  d_nm(nm),
  d_used(false),
  d_nv(&d_inlineNv),
  d_inlineNv(0),
  d_childrenStorage() {
  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(kind::UNDEFINED_KIND);
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder(NodeManager* nm, Kind k) :
  d_size(nchild_thresh),
  d_hash(0),
  d_nm(nm),
  d_used(false),
  d_nv(&d_inlineNv),
  d_inlineNv(0),
  d_childrenStorage() {

  d_inlineNv.d_kind = k;
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::~NodeBuilder() {
  if(!d_used) {
    // Warning("NodeBuilder unused at destruction\n");
    // Commented above, as it happens a lot, for example with exceptions
    dealloc();
  }
}

template <unsigned nchild_thresh>
void NodeBuilder<nchild_thresh>::clear(Kind k) {
  if(!d_used) {
    Warning("NodeBuilder unused at clear\n");

    dealloc();
  }

  d_size = nchild_thresh;
  d_hash = 0;
  d_nm = NodeManager::currentNM();
  d_used = false;
  d_nv = &d_inlineNv;
  d_inlineNv.d_kind = k;
  d_inlineNv.d_nchildren = 0;//FIXME leak
}

template <unsigned nchild_thresh>
void NodeBuilder<nchild_thresh>::realloc() {
  if(EXPECT_FALSE( nvIsAllocated() )) {
    d_nv = (expr::NodeValue*)
      std::realloc(d_nv,
                   sizeof(expr::NodeValue) + ( sizeof(expr::NodeValue*) * (d_size *= 2) ));
    if(d_nv == NULL) {
      throw std::bad_alloc();
    }
  } else {
    d_nv = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue) + ( sizeof(expr::NodeValue*) * (d_size *= 2) ));
    if(d_nv == NULL) {
      throw std::bad_alloc();
    }
    d_nv->d_id = 0;
    d_nv->d_rc = 0;
    d_nv->d_kind = d_inlineNv.d_kind;
    d_nv->d_nchildren = nchild_thresh;
    std::copy(d_inlineNv.d_children,
              d_inlineNv.d_children + nchild_thresh,
              d_nv->d_children);
  }
}

template <unsigned nchild_thresh>
void NodeBuilder<nchild_thresh>::realloc(size_t toSize, bool copy) {
  Assert( d_size < toSize );

  if(EXPECT_FALSE( nvIsAllocated() )) {
    d_nv = (expr::NodeValue*)
      std::realloc(d_nv, sizeof(expr::NodeValue) +
                   ( sizeof(expr::NodeValue*) * (d_size = toSize) ));
    if(d_nv == NULL) {
      throw std::bad_alloc();
    }
  } else {
    d_nv = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue) +
                  ( sizeof(expr::NodeValue*) * (d_size = toSize) ));
    if(d_nv == NULL) {
      throw std::bad_alloc();
    }
    d_nv->d_id = 0;
    d_nv->d_rc = 0;
    d_nv->d_kind = d_inlineNv.d_kind;
    d_nv->d_nchildren = nchild_thresh;
    if(copy) {
      std::copy(d_inlineNv.d_children,
                d_inlineNv.d_children + nchild_thresh,
                d_nv->d_children);
      // inhibit decr'ing refcounts of children in dtor
      d_inlineNv.d_nchildren = 0;
    }
  }
}

template <unsigned nchild_thresh>
inline void NodeBuilder<nchild_thresh>::dealloc() {
  /* Prefer asserts to if() because usually these conditions have been
   * checked already, so we don't want to do a double-check in
   * production; these are just sanity checks for debug builds */
  Assert(!d_used, "Internal error: NodeBuilder: dealloc() called with d_used");

  for(expr::NodeValue::nv_iterator i = d_nv->nv_begin();
      i != d_nv->nv_end();
      ++i) {
    (*i)->dec();
  }
  if(nvIsAllocated()) {
    free(d_nv);
  }
}

template <unsigned nchild_thresh>
NodeBuilder<nchild_thresh>::operator Node() const {// const version
  Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
  Assert(d_nv->getKind() != kind::UNDEFINED_KIND,
         "Can't make an expression of an undefined kind!");

  if(d_nv->d_kind == kind::VARIABLE) {
    Assert(d_nv->d_nchildren == 0);
    expr::NodeValue* nv = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue) +
                  (sizeof(expr::NodeValue*) * d_inlineNv.d_nchildren ));// FIXME :: WTF??
    if(nv == NULL) {
      throw std::bad_alloc();
    }
    nv->d_nchildren = 0;
    nv->d_kind = kind::VARIABLE;
    nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
    nv->d_rc = 0;
    //d_used = true; // const version
    //d_nv = NULL; // const version
    return Node(nv);
  }

  // implementation differs depending on whether the expression value
  // was malloc'ed or not

  if(EXPECT_FALSE( nvIsAllocated() )) {
    // Lookup the expression value in the pool we already have (with insert)
    expr::NodeValue* nv = d_nm->poolLookup(d_nv);
    // If something else is there, we reuse it
    if(nv != NULL) {
      // expression already exists in node manager
      //dealloc(); // const version
      //d_used = true; // const version
      return Node(nv);
    }
    // Otherwise copy children out
    nv = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue) +
                  ( sizeof(expr::NodeValue*) * d_nv->d_nchildren ));
    if(nv == NULL) {
      throw std::bad_alloc();
    }
    nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
    nv->d_rc = 0;
    nv->d_kind = d_nv->d_kind;
    nv->d_nchildren = d_nv->d_nchildren;
    std::copy(d_nv->d_children,
              d_nv->d_children + d_nv->d_nchildren,
              nv->d_children);
    // inc child refcounts
    for(expr::NodeValue::nv_iterator i = nv->nv_begin();
        i != nv->nv_end();
        ++i) {
      (*i)->inc();
    }
    d_nm->poolInsert(nv);
    return Node(nv);
  }

  // Lookup the expression value in the pool we already have
  expr::NodeValue* ev = d_nm->poolLookup(d_nv);
  //DANGER d_nv should be ptr-to-const in the above line b/c it points to d_inlineNv
  if(ev != NULL) {
    // expression already exists in node manager
    //d_used = true; // const version
    Debug("node") << "result: " << Node(ev) << std::endl;
    return Node(ev);
  }

  // otherwise create the canonical expression value for this node
  ev = (expr::NodeValue*)
    std::malloc(sizeof(expr::NodeValue) +
                ( sizeof(expr::NodeValue*) * d_inlineNv.d_nchildren ));
  if(ev == NULL) {
    throw std::bad_alloc();
  }
  ev->d_nchildren = d_inlineNv.d_nchildren;
  ev->d_kind = d_inlineNv.d_kind;
  ev->d_id = expr::NodeValue::next_id++;// FIXME multithreading
  ev->d_rc = 0;
  std::copy(d_inlineNv.d_children,
            d_inlineNv.d_children + d_inlineNv.d_nchildren,
            ev->d_children);
  //d_used = true;
  //d_nv = NULL;
  //d_inlineNv.d_nchildren = 0;// inhibit decr'ing refcounts of children in dtor
  // inc child refcounts
  for(expr::NodeValue::nv_iterator i = ev->nv_begin();
      i != ev->nv_end();
      ++i) {
    (*i)->inc();
  }

  // Make the new expression
  d_nm->poolInsert(ev);
  return Node(ev);
}

template <unsigned nchild_thresh>
NodeBuilder<nchild_thresh>::operator Node() {// not const
  Assert(!d_used, "NodeBuilder is one-shot only; attempt to access it after conversion");
  Assert(d_nv->getKind() != kind::UNDEFINED_KIND,
         "Can't make an expression of an undefined kind!");

  if(d_nv->d_kind == kind::VARIABLE) {
    Assert(d_nv->d_nchildren == 0);
    expr::NodeValue* nv = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue) +
                  (sizeof(expr::NodeValue*) * d_inlineNv.d_nchildren ));// FIXME :: WTF??
    if(nv == NULL) {
      throw std::bad_alloc();
    }
    nv->d_nchildren = 0;
    nv->d_kind = kind::VARIABLE;
    nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
    nv->d_rc = 0;
    d_used = true;
    d_nv = NULL;
    Debug("node") << "result: " << Node(nv) << std::endl;
    return Node(nv);
  }

  // implementation differs depending on whether the expression value
  // was malloc'ed or not

  if(EXPECT_FALSE( nvIsAllocated() )) {
    // Lookup the expression value in the pool we already have (with insert)
    expr::NodeValue* nv = d_nm->poolLookup(d_nv);
    // If something else is there, we reuse it
    if(nv != NULL) {
      // expression already exists in node manager
      dealloc();
      d_used = true;
      Debug("node") << "result: " << Node(nv) << std::endl;
      return Node(nv);
    }
    // Otherwise crop and set the expression value to the allocated one
    crop();
    nv = d_nv;
    nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
    d_nv = NULL;
    d_used = true;
    d_nm->poolInsert(nv);
    return Node(nv);
  }

  // Lookup the expression value in the pool we already have
  expr::NodeValue* ev = d_nm->poolLookup(&d_inlineNv);
  if(ev != NULL) {
    // expression already exists in node manager
    d_used = true;
    Debug("node") << "result: " << Node(ev) << std::endl;
    return Node(ev);
  }

  // otherwise create the canonical expression value for this node
  ev = (expr::NodeValue*)
    std::malloc(sizeof(expr::NodeValue) +
                ( sizeof(expr::NodeValue*) * d_inlineNv.d_nchildren ));
  if(ev == NULL) {
    throw std::bad_alloc();
  }
  ev->d_nchildren = d_inlineNv.d_nchildren;
  ev->d_kind = d_inlineNv.d_kind;
  ev->d_id = expr::NodeValue::next_id++;// FIXME multithreading
  ev->d_rc = 0;
  std::copy(d_inlineNv.d_children,
            d_inlineNv.d_children + d_inlineNv.d_nchildren,
            ev->d_children);
  d_used = true;
  d_nv = NULL;
  d_inlineNv.d_nchildren = 0;// inhibit decr'ing refcounts of children in dtor

  // Make the new expression
  d_nm->poolInsert(ev);
  return Node(ev);
}

template <unsigned nchild_thresh>
inline std::ostream& operator<<(std::ostream& out,
                                const NodeBuilder<nchild_thresh>& b) {
  b.toStream(out);
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__NODE_BUILDER_H */
