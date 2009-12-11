/*********************                                           -*- C++ -*-  */
/** expr_builder.h
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

#include "expr/node_manager.h"
#include "expr/kind.h"
#include "util/Assert.h"

namespace CVC4 {

class AndExprBuilder;
class OrExprBuilder;
class PlusExprBuilder;
class MinusExprBuilder;
class MultExprBuilder;

class NodeBuilder {
  NodeManager* d_em;

  Kind d_kind;

  // initially false, when you extract the Node this is set and you can't
  // extract another
  bool d_used;

  static const unsigned nchild_thresh = 10;

  unsigned d_nchildren;
  union {
    ExprValue*         u_arr[nchild_thresh];
    std::vector<Node>* u_vec;
  } d_children;

  void addChild(const Node& e) { addChild(e.d_ev); }
  void addChild(ExprValue*);
  NodeBuilder& collapse();

  typedef ExprValue** ev_iterator;
  typedef ExprValue const** const_ev_iterator;

  ev_iterator ev_begin() {
    return d_children.u_arr;
  }

  ev_iterator ev_end() {
    return d_children.u_arr + d_nchildren;
  }

  NodeBuilder& reset(const ExprValue*);

public:

  NodeBuilder();
  NodeBuilder(Kind k);
  NodeBuilder(const Node&);
  NodeBuilder(const NodeBuilder&);

  NodeBuilder(NodeManager*);
  NodeBuilder(NodeManager*, Kind k);
  NodeBuilder(NodeManager*, const Node&);
  NodeBuilder(NodeManager*, const NodeBuilder&);

  ~NodeBuilder();

  // Compound expression constructors
  NodeBuilder& eqExpr(const Node& right);
  NodeBuilder& notExpr();
  NodeBuilder& andExpr(const Node& right);
  NodeBuilder& orExpr(const Node& right);
  NodeBuilder& iteExpr(const Node& thenpart, const Node& elsepart);
  NodeBuilder& iffExpr(const Node& right);
  NodeBuilder& impExpr(const Node& right);
  NodeBuilder& xorExpr(const Node& right);

  /* TODO design: these modify NodeBuilder */
  NodeBuilder& operator!() { return notExpr(); }
  NodeBuilder& operator&&(const Node& right) { return andExpr(right); }
  NodeBuilder& operator||(const Node& right) { return orExpr(right);  }

  // "Stream" expression constructor syntax
  NodeBuilder& operator<<(const Kind& op);
  NodeBuilder& operator<<(const Node& child);

  // For pushing sequences of children
  NodeBuilder& append(const std::vector<Node>& children) { return append(children.begin(), children.end()); }
  NodeBuilder& append(Node child) { return append(&child, (&child) + 1); }
  template <class Iterator> NodeBuilder& append(const Iterator& begin, const Iterator& end);

  operator Node();// not const

  AndExprBuilder   operator&&(Node);
  OrExprBuilder    operator||(Node);
  PlusExprBuilder  operator+ (Node);
  PlusExprBuilder  operator- (Node);
  MultExprBuilder  operator* (Node);

  friend class AndExprBuilder;
  friend class OrExprBuilder;
  friend class PlusExprBuilder;
  friend class MultExprBuilder;
};/* class NodeBuilder */

class AndExprBuilder {
  NodeBuilder d_eb;

public:

  AndExprBuilder(const NodeBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != AND) {
      d_eb.collapse();
      d_eb.d_kind = AND;
    }
  }

  AndExprBuilder&   operator&&(Node);
  OrExprBuilder     operator||(Node);

  operator NodeBuilder() { return d_eb; }

};/* class AndExprBuilder */

class OrExprBuilder {
  NodeBuilder d_eb;

public:

  OrExprBuilder(const NodeBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != OR) {
      d_eb.collapse();
      d_eb.d_kind = OR;
    }
  }

  AndExprBuilder    operator&&(Node);
  OrExprBuilder&    operator||(Node);

  operator NodeBuilder() { return d_eb; }

};/* class OrExprBuilder */

class PlusExprBuilder {
  NodeBuilder d_eb;

public:

  PlusExprBuilder(const NodeBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != PLUS) {
      d_eb.collapse();
      d_eb.d_kind = PLUS;
    }
  }

  PlusExprBuilder&  operator+(Node);
  PlusExprBuilder&  operator-(Node);
  MultExprBuilder   operator*(Node);

  operator NodeBuilder() { return d_eb; }

};/* class PlusExprBuilder */

class MultExprBuilder {
  NodeBuilder d_eb;

public:

  MultExprBuilder(const NodeBuilder& eb) : d_eb(eb) {
    if(d_eb.d_kind != MULT) {
      d_eb.collapse();
      d_eb.d_kind = MULT;
    }
  }

  PlusExprBuilder   operator+(Node);
  PlusExprBuilder   operator-(Node);
  MultExprBuilder&  operator*(Node);

  operator NodeBuilder() { return d_eb; }

};/* class MultExprBuilder */

template <class Iterator>
inline NodeBuilder& NodeBuilder::append(const Iterator& begin, const Iterator& end) {
  for(Iterator i = begin; i != end; ++i)
    addChild(*i);
  return *this;
}

// not const
inline NodeBuilder::operator Node() {
  ExprValue *ev;
  uint64_t hash;

  Assert(d_kind != UNDEFINED_KIND, "Can't make an expression of an undefined kind!");

  // variables are permitted to be duplicates (from POV of the expression manager)
  if(d_kind == VARIABLE) {
    ev = new ExprValue;
    ev->d_kind = d_kind;
    ev->d_id = ExprValue::next_id++;// FIXME multithreading
    return Node(ev);
  } else {
    if(d_nchildren <= nchild_thresh) {
      hash = ExprValue::computeHash<ev_iterator>(d_kind, ev_begin(), ev_end());
      void *space = std::calloc(1, sizeof(ExprValue) + d_nchildren * sizeof(Node));
      ev = new (space) ExprValue;
      size_t nc = 0;
      ev_iterator i = ev_begin();
      ev_iterator i_end = ev_end();
      for(; i != i_end; ++i) {
        // The expressions in the allocated children are all 0, so we must
        // construct it without using an assignment operator
        ev->d_children[nc++].assignExprValue(*i);
      }
    } else {
      hash = ExprValue::computeHash<std::vector<Node>::const_iterator>(d_kind, d_children.u_vec->begin(), d_children.u_vec->end());
      void *space = std::calloc(1, sizeof(ExprValue) + d_nchildren * sizeof(Node));
      ev = new (space) ExprValue;
      size_t nc = 0;
      for(std::vector<Node>::iterator i = d_children.u_vec->begin(); i != d_children.u_vec->end(); ++i)
        ev->d_children[nc++] = Node(*i);
    }
  }

  ev->d_nchildren = d_nchildren;
  ev->d_kind = d_kind;
  ev->d_id = ExprValue::next_id++;// FIXME multithreading
  ev->d_rc = 0;
  Node e(ev);

  return d_em->lookup(hash, e);
}

inline AndExprBuilder   NodeBuilder::operator&&(Node e) {
  return AndExprBuilder(*this) && e;
}

inline OrExprBuilder    NodeBuilder::operator||(Node e) {
  return OrExprBuilder(*this) || e;
}

inline PlusExprBuilder  NodeBuilder::operator+ (Node e) {
  return PlusExprBuilder(*this) + e;
}

inline PlusExprBuilder  NodeBuilder::operator- (Node e) {
  return PlusExprBuilder(*this) - e;
}

inline MultExprBuilder  NodeBuilder::operator* (Node e) {
  return MultExprBuilder(*this) * e;
}

inline AndExprBuilder&  AndExprBuilder::operator&&(Node e) {
  d_eb.append(e);
  return *this;
}

inline OrExprBuilder    AndExprBuilder::operator||(Node e) {
  return OrExprBuilder(d_eb.collapse()) || e;
}

inline AndExprBuilder   OrExprBuilder::operator&&(Node e) {
  return AndExprBuilder(d_eb.collapse()) && e;
}

inline OrExprBuilder&   OrExprBuilder::operator||(Node e) {
  d_eb.append(e);
  return *this;
}

inline PlusExprBuilder& PlusExprBuilder::operator+(Node e) {
  d_eb.append(e);
  return *this;
}

inline PlusExprBuilder& PlusExprBuilder::operator-(Node e) {
  d_eb.append(e.uMinusExpr());
  return *this;
}

inline MultExprBuilder  PlusExprBuilder::operator*(Node e) {
  return MultExprBuilder(d_eb.collapse()) * e;
}

inline PlusExprBuilder  MultExprBuilder::operator+(Node e) {
  return MultExprBuilder(d_eb.collapse()) + e;
}

inline PlusExprBuilder  MultExprBuilder::operator-(Node e) {
  return MultExprBuilder(d_eb.collapse()) - e;
}

inline MultExprBuilder& MultExprBuilder::operator*(Node e) {
  d_eb.append(e);
  return *this;
}


}/* CVC4 namespace */

#endif /* __CVC4__NODE_BUILDER_H */
