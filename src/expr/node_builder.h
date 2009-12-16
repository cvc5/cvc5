/*********************                                           -*- C++ -*-  */
/** node_builder.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

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

namespace CVC4 {

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

  NodeValue *d_ev;
  NodeValue d_inlineEv;
  NodeValue *d_childrenStorage[nchild_thresh];

  bool evIsAllocated() {
    return d_ev->d_nchildren > nchild_thresh;
  }

  template <unsigned N>
  bool evIsAllocated(const NodeBuilder<N>& nb) {
    return nb.d_ev->d_nchildren > N;
  }

  bool evNeedsToBeAllocated() {
    return d_ev->d_nchildren == d_size;
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

public:

  inline NodeBuilder();
  inline NodeBuilder(Kind k);
  inline NodeBuilder(const NodeBuilder<nchild_thresh>& nb);
  template <unsigned N> inline NodeBuilder(const NodeBuilder<N>& nb);
  inline NodeBuilder(NodeManager* nm);
  inline NodeBuilder(NodeManager* nm, Kind k);
  inline ~NodeBuilder();

  typedef NodeValue::ev_iterator iterator;
  typedef NodeValue::const_ev_iterator const_iterator;

  iterator begin() { return d_ev->ev_begin(); }
  iterator end() { return d_ev->ev_end(); }
  const_iterator begin() const { return d_ev->ev_begin(); }
  const_iterator end() const { return d_ev->ev_end(); }

  // Compound expression constructors
  /*
  NodeBuilder& eqExpr(const Node& right);
  NodeBuilder& notExpr();
  NodeBuilder& andExpr(const Node& right);
  NodeBuilder& orExpr(const Node& right);
  NodeBuilder& iteExpr(const Node& thenpart, const Node& elsepart);
  NodeBuilder& iffExpr(const Node& right);
  NodeBuilder& impExpr(const Node& right);
  NodeBuilder& xorExpr(const Node& right);
  */

  /* TODO design: these modify NodeBuilder ?? */
  /*
  NodeBuilder& operator!() { return notExpr(); }
  NodeBuilder& operator&&(const Node& right) { return andExpr(right); }
  NodeBuilder& operator||(const Node& right) { return orExpr(right);  }
  */

  /*
  NodeBuilder& operator&&=(const Node& right) { return andExpr(right); }
  NodeBuilder& operator||=(const Node& right) { return orExpr(right);  }
  */

  // "Stream" expression constructor syntax

  NodeBuilder& operator<<(const Kind& k) {
    Assert(d_ev->d_kind == UNDEFINED_KIND);
    d_ev->d_kind = k;
    return *this;
  }

  NodeBuilder& operator<<(const Node& n) {
    return append(n);
  }

  // For pushing sequences of children
  NodeBuilder& append(const std::vector<Node>& children) {
    return append(children.begin(), children.end());
  }

  NodeBuilder& append(const Node& n) {
    allocateEvIfNecessaryForAppend();
    NodeValue* ev = n.d_ev;
    d_hash = NodeValue::computeHash(d_hash, ev);
    ev->inc();
    d_ev->d_children[d_ev->d_nchildren++] = ev;
    return *this;
  }

  template <class Iterator>
  NodeBuilder& append(const Iterator& begin, const Iterator& end) {
    for(Iterator i = begin; i != end; ++i) {
      append(*i);
    }
    return *this;
  }

  void crop() {
    if(EXPECT_FALSE( evIsAllocated() ) && d_size > d_ev->d_nchildren) {
      d_ev = (NodeValue*)
        std::realloc(d_ev, sizeof(NodeValue) +
                     ( sizeof(NodeValue*) * (d_size = d_ev->d_nchildren) ));
    }
  }

  // not const
  operator Node();

  /*
  AndNodeBuilder   operator&&(Node);
  OrNodeBuilder    operator||(Node);
  PlusNodeBuilder  operator+ (Node);
  PlusNodeBuilder  operator- (Node);
  MultNodeBuilder  operator* (Node);

  friend class AndNodeBuilder;
  friend class OrNodeBuilder;
  friend class PlusNodeBuilder;
  friend class MultNodeBuilder;
  */
};/* class NodeBuilder */

#if 0
class AndNodeBuilder {
  NodeBuilder d_eb;

public:

  AndNodeBuilder(const NodeBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != AND) {
      d_eb.collapse();
      d_eb.d_kind = AND;
    }
  }

  AndNodeBuilder&   operator&&(Node);
  OrNodeBuilder     operator||(Node);

  operator NodeBuilder() { return d_eb; }

};/* class AndNodeBuilder */

class OrNodeBuilder {
  NodeBuilder d_eb;

public:

  OrNodeBuilder(const NodeBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != OR) {
      d_eb.collapse();
      d_eb.d_kind = OR;
    }
  }

  AndNodeBuilder    operator&&(Node);
  OrNodeBuilder&    operator||(Node);

  operator NodeBuilder() { return d_eb; }

};/* class OrNodeBuilder */

class PlusNodeBuilder {
  NodeBuilder d_eb;

public:

  PlusNodeBuilder(const NodeBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != PLUS) {
      d_eb.collapse();
      d_eb.d_kind = PLUS;
    }
  }

  PlusNodeBuilder&  operator+(Node);
  PlusNodeBuilder&  operator-(Node);
  MultNodeBuilder   operator*(Node);

  operator NodeBuilder() { return d_eb; }

};/* class PlusNodeBuilder */

class MultNodeBuilder {
  NodeBuilder d_eb;

public:

  MultNodeBuilder(const NodeBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != MULT) {
      d_eb.collapse();
      d_eb.d_kind = MULT;
    }
  }

  PlusNodeBuilder   operator+(Node);
  PlusNodeBuilder   operator-(Node);
  MultNodeBuilder&  operator*(Node);

  operator NodeBuilder() { return d_eb; }

};/* class MultNodeBuilder */

inline AndNodeBuilder   NodeBuilder::operator&&(Node e) {
  return AndNodeBuilder(*this) && e;
}

inline OrNodeBuilder    NodeBuilder::operator||(Node e) {
  return OrNodeBuilder(*this) || e;
}

inline PlusNodeBuilder  NodeBuilder::operator+ (Node e) {
  return PlusNodeBuilder(*this) + e;
}

inline PlusNodeBuilder  NodeBuilder::operator- (Node e) {
  return PlusNodeBuilder(*this) - e;
}

inline MultNodeBuilder  NodeBuilder::operator* (Node e) {
  return MultNodeBuilder(*this) * e;
}

inline AndNodeBuilder&  AndNodeBuilder::operator&&(Node e) {
  d_eb.append(e);
  return *this;
}

inline OrNodeBuilder    AndNodeBuilder::operator||(Node e) {
  return OrNodeBuilder(d_eb.collapse()) || e;
}

inline AndNodeBuilder   OrNodeBuilder::operator&&(Node e) {
  return AndNodeBuilder(d_eb.collapse()) && e;
}

inline OrNodeBuilder&   OrNodeBuilder::operator||(Node e) {
  d_eb.append(e);
  return *this;
}

inline PlusNodeBuilder& PlusNodeBuilder::operator+(Node e) {
  d_eb.append(e);
  return *this;
}

inline PlusNodeBuilder& PlusNodeBuilder::operator-(Node e) {
  d_eb.append(e.uMinusExpr());
  return *this;
}

inline MultNodeBuilder  PlusNodeBuilder::operator*(Node e) {
  return MultNodeBuilder(d_eb.collapse()) * e;
}

inline PlusNodeBuilder  MultNodeBuilder::operator+(Node e) {
  return MultNodeBuilder(d_eb.collapse()) + e;
}

inline PlusNodeBuilder  MultNodeBuilder::operator-(Node e) {
  return MultNodeBuilder(d_eb.collapse()) - e;
}

inline MultNodeBuilder& MultNodeBuilder::operator*(Node e) {
  d_eb.append(e);
  return *this;
}

#endif /* 0 */

}/* CVC4 namespace */

#include "expr/node.h"
#include "expr/node_manager.h"

// template implementations

namespace CVC4 {

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder() :
  d_size(nchild_thresh),
  d_nm(NodeManager::currentNM()),
  d_used(false),
  d_ev(&d_inlineEv),
  d_inlineEv(0),
  d_childrenStorage(0) {}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder(Kind k) :
  d_size(nchild_thresh),
  d_nm(NodeManager::currentNM()),
  d_used(false),
  d_ev(&d_inlineEv),
  d_inlineEv(0),
  d_childrenStorage(0) {

  d_inlineEv.d_kind = k;
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder(const NodeBuilder<nchild_thresh>& nb) :
  d_size(nchild_thresh),
  d_nm(nb.d_nm),
  d_used(nb.d_used),
  d_ev(&d_inlineEv),
  d_inlineEv(0),
  d_childrenStorage(0) {

  if(evIsAllocated(nb)) {
    realloc(nb->d_size, false);
    std::copy(d_ev->begin(), nb.d_ev->begin(), nb.d_ev->end());
  } else {
    std::copy(d_inlineEv.begin(), nb.d_ev->begin(), nb.d_ev->end());
  }
}

template <unsigned nchild_thresh>
template <unsigned N>
inline NodeBuilder<nchild_thresh>::NodeBuilder(const NodeBuilder<N>& nb) :
  d_size(nchild_thresh),
  d_nm(NodeManager::currentNM()),
  d_used(nb.d_used),
  d_ev(&d_inlineEv),
  d_inlineEv(0),
  d_childrenStorage(0) {

  if(nb.d_ev->d_nchildren > nchild_thresh) {
    realloc(nb.d_size, false);
    std::copy(d_ev->begin(), nb.d_ev->begin(), nb.d_ev->end());
  } else {
    std::copy(d_inlineEv.begin(), nb.d_ev->begin(), nb.d_ev->end());
  }
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder(NodeManager* nm) :
  d_size(nchild_thresh),
  d_nm(nm),
  d_used(false),
  d_ev(&d_inlineEv),
  d_inlineEv(0),
  d_childrenStorage(0) {}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::NodeBuilder(NodeManager* nm, Kind k) :
  d_size(nchild_thresh),
  d_nm(nm),
  d_used(false),
  d_ev(&d_inlineEv),
  d_inlineEv(0),
  d_childrenStorage() {

  d_inlineEv.d_kind = k;
}

template <unsigned nchild_thresh>
inline NodeBuilder<nchild_thresh>::~NodeBuilder() {
  for(iterator i = begin();
      i != end();
      ++i) {
    (*i)->dec();
  }
  if(evIsAllocated()) {
    free(d_ev);
  }
}

template <unsigned nchild_thresh>
void NodeBuilder<nchild_thresh>::realloc() {
  if(EXPECT_FALSE( evIsAllocated() )) {
    d_ev = (NodeValue*)
      std::realloc(d_ev,
                   sizeof(NodeValue) + ( sizeof(NodeValue*) * (d_size *= 2) ));
  } else {
    d_ev = (NodeValue*)
      std::malloc(sizeof(NodeValue) + ( sizeof(NodeValue*) * (d_size *= 2) ));
    d_ev->d_id = 0;
    d_ev->d_rc = 0;
    d_ev->d_kind = d_inlineEv.d_kind;
    d_ev->d_nchildren = nchild_thresh;
    std::copy(d_ev->d_children,
              d_inlineEv.d_children,
              d_inlineEv.d_children + nchild_thresh);
  }
}

template <unsigned nchild_thresh>
void NodeBuilder<nchild_thresh>::realloc(size_t toSize, bool copy) {
  Assert( d_size < toSize );

  if(EXPECT_FALSE( evIsAllocated() )) {
    d_ev = (NodeValue*)
      std::realloc(d_ev, sizeof(NodeValue) +
                   ( sizeof(NodeValue*) * (d_size = toSize) ));
  } else {
    d_ev = (NodeValue*)
      std::malloc(sizeof(NodeValue) +
                  ( sizeof(NodeValue*) * (d_size = toSize) ));
    d_ev->d_id = 0;
    d_ev->d_rc = 0;
    d_ev->d_kind = d_inlineEv.d_kind;
    d_ev->d_nchildren = nchild_thresh;
    if(copy) {
      std::copy(d_ev->d_children,
                d_inlineEv.d_children,
                d_inlineEv.d_children + nchild_thresh);
    }
  }
}

template <unsigned nchild_thresh>
NodeBuilder<nchild_thresh>::operator Node() {// not const
  Assert(d_ev->d_kind != UNDEFINED_KIND,
         "Can't make an expression of an undefined kind!");
  Assert(! d_used, "This NodeBuilder has already been used!");

  // implementation differs depending on whether the expression value
  // was malloc'ed or not

  if(EXPECT_FALSE( evIsAllocated() )) {
    NodeValue *ev = d_nm->lookupNoInsert(d_hash, d_ev);
    if(ev != d_ev) {
      // expression already exists in node manager
      return Node(ev);
    }

    // otherwise create the canonical expression value for this node
    crop();
    d_used = true;
    ev = d_ev;
    d_ev = NULL;
    // this inserts into the NodeManager;
    // return the result of lookup() in case another thread beat us to it
    return d_nm->lookup(d_hash, ev);
  }

  NodeValue *ev = d_nm->lookupNoInsert(d_hash, &d_inlineEv);
  if(ev != &d_inlineEv) {
    // expression already exists in node manager
    return Node(ev);
  }

  // otherwise create the canonical expression value for this node
  ev = (NodeValue*)
    std::malloc(sizeof(NodeValue) +
                ( sizeof(NodeValue*) * d_inlineEv.d_nchildren) );
  ev->d_nchildren = d_ev->d_nchildren;
  ev->d_kind = d_ev->d_kind;
  ev->d_id = NodeValue::next_id++;// FIXME multithreading
  ev->d_rc = 0;
  d_used = true;
  d_ev = NULL;

  // this inserts into the NodeManager;
  // return the result of lookup() in case another thread beat us to it
  return d_nm->lookup(d_hash, ev);
}

}/* CVC4 namespace */

#endif /* __CVC4__NODE_BUILDER_H */
