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
class MinusNodeBuilder;
class MultNodeBuilder;

template <unsigned nchild_thresh>
class NodeBuilder {

  unsigned d_size;

  uint64_t d_hash;

  NodeManager* d_nm;

  // initially false, when you extract the Node this is set and you can't
  // extract another
  bool d_used;

  NodeValue *d_nv;
  NodeValue d_inlineNv;
  NodeValue *d_childrenStorage[nchild_thresh];

  bool nvIsAllocated() {
    return d_nv->d_nchildren > nchild_thresh;
  }

  template <unsigned N>
  bool nvIsAllocated(const NodeBuilder<N>& nb) {
    return nb.d_nv->d_nchildren > N;
  }

  bool evNeedsToBeAllocated() {
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
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    if(EXPECT_FALSE( nvIsAllocated() ) && EXPECT_TRUE( d_size > d_nv->d_nchildren )) {
      d_nv = (NodeValue*)
        std::realloc(d_nv, sizeof(NodeValue) +
                     ( sizeof(NodeValue*) * (d_size = d_nv->d_nchildren) ));
    }
  }

public:

  inline NodeBuilder();
  inline NodeBuilder(Kind k);
  inline NodeBuilder(const NodeBuilder<nchild_thresh>& nb);
  template <unsigned N> inline NodeBuilder(const NodeBuilder<N>& nb);
  inline NodeBuilder(NodeManager* nm);
  inline NodeBuilder(NodeManager* nm, Kind k);
  inline ~NodeBuilder();

  typedef NodeValue::iterator<true> iterator;
  typedef NodeValue::iterator<true> const_iterator;

  const_iterator begin() const {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    return d_nv->begin<true>();
  }

  const_iterator end() const {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    return d_nv->end<true>();
  }

  Kind getKind() const {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    return d_nv->getKind();
  }

  unsigned getNumChildren() const {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    return d_nv->getNumChildren();
  }

  Node operator[](int i) const {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    Assert(i >= 0 && i < d_nv->getNumChildren());
    return Node(d_nv->d_children[i]);
  }

  void clear(Kind k = kind::UNDEFINED_KIND);

  // Compound expression constructors
  /*
  NodeBuilder& eqExpr(TNode right);
  NodeBuilder& notExpr();
  NodeBuilder& andExpr(TNode right);
  NodeBuilder& orExpr(TNode right);
  NodeBuilder& iteExpr(TNode thenpart, TNode elsepart);
  NodeBuilder& iffExpr(TNode right);
  NodeBuilder& impExpr(TNode right);
  NodeBuilder& xorExpr(TNode right);
  */

  /* TODO design: these modify NodeBuilder ?? */
  /*
  NodeBuilder& operator!() { return notExpr(); }
  NodeBuilder& operator&&(TNode right) { return andExpr(right); }
  NodeBuilder& operator||(TNode right) { return orExpr(right);  }
  */

  /*
  NodeBuilder& operator&&=(TNode right) { return andExpr(right); }
  NodeBuilder& operator||=(TNode right) { return orExpr(right);  }
  */

  // "Stream" expression constructor syntax

  NodeBuilder& operator<<(const Kind& k) {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    Assert(d_nv->getKind() == kind::UNDEFINED_KIND);
    d_nv->d_kind = k;
    return *this;
  }

  NodeBuilder& operator<<(TNode n) {
    // FIXME: collapse if ! UNDEFINED_KIND
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    return append(n);
  }

  // For pushing sequences of children
  NodeBuilder& append(const std::vector<Node>& children) {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    return append(children.begin(), children.end());
  }

  NodeBuilder& append(TNode n) {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    Debug("prop") << "append: " << this << " " << n << "[" << n.d_nv << "]" << std::endl;
    allocateEvIfNecessaryForAppend();
    NodeValue* ev = n.d_nv;
    ev->inc();
    d_nv->d_children[d_nv->d_nchildren++] = ev;
    return *this;
  }

  template <class Iterator>
  NodeBuilder& append(const Iterator& begin, const Iterator& end) {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    for(Iterator i = begin; i != end; ++i) {
      append(*i);
    }
    return *this;
  }

  // not const
  operator Node();

  inline void toStream(std::ostream& out) const {
    Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
    d_nv->toStream(out);
  }

  AndNodeBuilder   operator&&(Node);
  OrNodeBuilder    operator||(Node);
  PlusNodeBuilder  operator+ (Node);
  PlusNodeBuilder  operator- (Node);
  MultNodeBuilder  operator* (Node);

  friend class AndNodeBuilder;
  friend class OrNodeBuilder;
  friend class PlusNodeBuilder;
  friend class MultNodeBuilder;
  
  //Yet 1 more example of how terrifying C++ is as a language
  //This is needed for copy constructors of different sizes to access private fields
  template <unsigned N> friend class NodeBuilder;

};/* class NodeBuilder */

class AndNodeBuilder {
  NodeBuilder<> d_eb;

public:

  AndNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    if(d_eb.d_nv->d_kind != kind::AND) {
      Node n = d_eb;
      d_eb.clear();
      d_eb.d_nv->d_kind = kind::AND;
      d_eb.append(n);
    }
  }

  AndNodeBuilder&   operator&&(Node);
  OrNodeBuilder     operator||(Node);

  operator NodeBuilder<>() { return d_eb; }

};/* class AndNodeBuilder */

class OrNodeBuilder {
  NodeBuilder<> d_eb;

public:

  OrNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    if(d_eb.d_nv->d_kind != kind::OR) {
      Node n = d_eb;
      d_eb.clear();
      d_eb.d_nv->d_kind = kind::OR;
      d_eb.append(n);
    }
  }

  AndNodeBuilder    operator&&(Node);
  OrNodeBuilder&    operator||(Node);

  operator NodeBuilder<>() { return d_eb; }

};/* class OrNodeBuilder */

class PlusNodeBuilder {
  NodeBuilder<> d_eb;

public:

  PlusNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    if(d_eb.d_nv->d_kind != kind::PLUS) {
      Node n = d_eb;
      d_eb.clear();
      d_eb.d_nv->d_kind = kind::PLUS;
      d_eb.append(n);
    }
  }

  PlusNodeBuilder&  operator+(Node);
  PlusNodeBuilder&  operator-(Node);
  MultNodeBuilder   operator*(Node);

  operator NodeBuilder<>() { return d_eb; }

};/* class PlusNodeBuilder */

class MultNodeBuilder {
  NodeBuilder<> d_eb;

public:

  MultNodeBuilder(const NodeBuilder<>& eb) : d_eb(eb) {
    if(d_eb.d_nv->d_kind != kind::MULT) {
      Node n = d_eb;
      d_eb.clear();
      d_eb.d_nv->d_kind = kind::MULT;
      d_eb.append(n);
    }
  }

  PlusNodeBuilder   operator+(Node);
  PlusNodeBuilder   operator-(Node);
  MultNodeBuilder&  operator*(Node);

  operator NodeBuilder<>() { return d_eb; }

};/* class MultNodeBuilder */

template <unsigned nchild_thresh>
inline AndNodeBuilder   NodeBuilder<nchild_thresh>::operator&&(Node e) {
  return AndNodeBuilder(*this) && e;
}

template <unsigned nchild_thresh>
inline OrNodeBuilder    NodeBuilder<nchild_thresh>::operator||(Node e) {
  return OrNodeBuilder(*this) || e;
}

template <unsigned nchild_thresh>
inline PlusNodeBuilder  NodeBuilder<nchild_thresh>::operator+ (Node e) {
  return PlusNodeBuilder(*this) + e;
}

template <unsigned nchild_thresh>
inline PlusNodeBuilder  NodeBuilder<nchild_thresh>::operator- (Node e) {
  return PlusNodeBuilder(*this) - e;
}

template <unsigned nchild_thresh>
inline MultNodeBuilder  NodeBuilder<nchild_thresh>::operator* (Node e) {
  return MultNodeBuilder(*this) * e;
}

inline AndNodeBuilder&  AndNodeBuilder::operator&&(Node e) {
  d_eb.append(e);
  return *this;
}

inline OrNodeBuilder    AndNodeBuilder::operator||(Node e) {
  Node n = d_eb;
  d_eb.clear();
  d_eb.append(n);
  return OrNodeBuilder(d_eb) || e;
}

inline AndNodeBuilder   OrNodeBuilder::operator&&(Node e) {
  Node n = d_eb;
  d_eb.clear();
  d_eb.append(n);
  return AndNodeBuilder(d_eb) && e;
}

inline OrNodeBuilder&   OrNodeBuilder::operator||(Node e) {
  d_eb.append(e);
  return *this;
}

inline PlusNodeBuilder& PlusNodeBuilder::operator+(Node e) {
  d_eb.append(e);
  return *this;
}

/*
inline PlusNodeBuilder& PlusNodeBuilder::operator-(Node e) {
  d_eb.append(e.uMinusExpr());
  return *this;
}
*/

inline MultNodeBuilder  PlusNodeBuilder::operator*(Node e) {
  Node n = d_eb;
  d_eb.clear();
  d_eb.append(n);
  return MultNodeBuilder(d_eb) * e;
}

inline PlusNodeBuilder  MultNodeBuilder::operator+(Node e) {
  Node n = d_eb;
  d_eb.clear();
  d_eb.append(n);
  return MultNodeBuilder(d_eb) + e;
}

inline PlusNodeBuilder  MultNodeBuilder::operator-(Node e) {
  Node n = d_eb;
  d_eb.clear();
  d_eb.append(n);
  return MultNodeBuilder(d_eb) - e;
}

inline MultNodeBuilder& MultNodeBuilder::operator*(Node e) {
  d_eb.append(e);
  return *this;
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

  //Message() << "kind " << k << std::endl;
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
  d_inlineNv.d_kind = NodeValue::kindToDKind(kind::UNDEFINED_KIND);
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

  //Message() << "kind " << k << std::endl;
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
    d_nv = (NodeValue*)
      std::realloc(d_nv,
                   sizeof(NodeValue) + ( sizeof(NodeValue*) * (d_size *= 2) ));
  } else {
    d_nv = (NodeValue*)
      std::malloc(sizeof(NodeValue) + ( sizeof(NodeValue*) * (d_size *= 2) ));
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
    d_nv = (NodeValue*)
      std::realloc(d_nv, sizeof(NodeValue) +
                   ( sizeof(NodeValue*) * (d_size = toSize) ));
  } else {
    d_nv = (NodeValue*)
      std::malloc(sizeof(NodeValue) +
                  ( sizeof(NodeValue*) * (d_size = toSize) ));
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
  Assert(!d_used,
         "Internal error: NodeBuilder: dealloc() called with d_used");

  for(NodeValue::nv_iterator i = d_nv->nv_begin();
      i != d_nv->nv_end();
      ++i) {
    (*i)->dec();
  }
  if(nvIsAllocated()) {
    free(d_nv);
  }
}

template <unsigned nchild_thresh>
NodeBuilder<nchild_thresh>::operator Node() {// not const
  Assert(!d_used, "NodeBuilder is one-shot only; tried to access it after conversion");
  Assert(d_nv->getKind() != kind::UNDEFINED_KIND,
         "Can't make an expression of an undefined kind!");

  if(d_nv->d_kind == kind::VARIABLE) {
    Assert(d_nv->d_nchildren == 0);
    NodeValue *nv = (NodeValue*)
      std::malloc(sizeof(NodeValue) +
                  (sizeof(NodeValue*) * d_inlineNv.d_nchildren ));// FIXME :: WTF??
    nv->d_nchildren = 0;
    nv->d_kind = kind::VARIABLE;
    nv->d_id = NodeValue::next_id++;// FIXME multithreading
    nv->d_rc = 0;
    d_used = true;
    d_nv = NULL;
    Debug("prop") << "result: " << Node(nv) << std::endl;
    return Node(nv);
  }

  // implementation differs depending on whether the expression value
  // was malloc'ed or not

  if(EXPECT_FALSE( nvIsAllocated() )) {
    // Lookup the expression value in the pool we already have (with insert)
    NodeValue* nv = d_nm->poolLookup(d_nv);
    // If something else is there, we reuse it
    if(nv != NULL) {
      // expression already exists in node manager
      dealloc();
      d_used = true;
      Debug("prop") << "result: " << Node(nv) << std::endl;
      return Node(nv);
    }
    // Otherwise crop and set the expression value to the allocate one
    crop();
    nv = d_nv;
    d_nv = NULL;
    d_used = true;
    d_nm->poolInsert(nv);
    Node n(nv);
    Debug("prop") << "result: " << n << std::endl;
    return n;
  }

  // Lookup the expression value in the pool we already have
  NodeValue* ev = d_nm->poolLookup(&d_inlineNv);
  if(ev != NULL) {
    // expression already exists in node manager
    d_used = true;
    Debug("prop") << "result: " << Node(ev) << std::endl;
    return Node(ev);
  }

  // otherwise create the canonical expression value for this node
  ev = (NodeValue*)
    std::malloc(sizeof(NodeValue) +
                ( sizeof(NodeValue*) * d_inlineNv.d_nchildren ));
  ev->d_nchildren = d_inlineNv.d_nchildren;
  ev->d_kind = d_inlineNv.d_kind;
  ev->d_id = NodeValue::next_id++;// FIXME multithreading
  ev->d_rc = 0;
  std::copy(d_inlineNv.d_children,
            d_inlineNv.d_children + d_inlineNv.d_nchildren,
            ev->d_children);
  d_used = true;
  d_nv = NULL;
  d_inlineNv.d_nchildren = 0;// inhibit decr'ing refcounts of children in dtor

  // Make the new expression
  d_nm->poolInsert(ev);
  Node n(ev);
  Debug("prop") << "result: " << n << std::endl;
  return n;
}

template <unsigned nchild_thresh>
inline std::ostream& operator<<(std::ostream& out,
                                const NodeBuilder<nchild_thresh>& b) {

  b.toStream(out);
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__NODE_BUILDER_H */
