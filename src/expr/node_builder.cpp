/*********************                                           -*- C++ -*-  */
/** expr_builder.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#include "expr/node_builder.h"
#include "expr/node_manager.h"
#include "expr/expr_value.h"
#include "util/output.h"

using namespace std;

namespace CVC4 {

NodeBuilder::NodeBuilder() :
  d_em(NodeManager::currentEM()), d_kind(UNDEFINED_KIND), d_used(false),
      d_nchildren(0) {
}

NodeBuilder::NodeBuilder(Kind k) :
  d_em(NodeManager::currentEM()), d_kind(k), d_used(false), d_nchildren(0) {
}

NodeBuilder::NodeBuilder(const Node& e) :
  d_em(NodeManager::currentEM()), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(1) {
  d_children.u_arr[0] = e.d_ev->inc();;
}

NodeBuilder& NodeBuilder::reset(const ExprValue* ev) {
  this->~NodeBuilder();
  d_kind = Kind(ev->d_kind);
  d_used = false;
  d_nchildren = ev->d_nchildren;
  for(Node::const_iterator i = ev->begin(); i != ev->end(); ++i)
    addChild(i->d_ev);
  return *this;
}

NodeBuilder::NodeBuilder(const NodeBuilder& eb) :
  d_em(eb.d_em), d_kind(eb.d_kind), d_used(eb.d_used),
      d_nchildren(eb.d_nchildren) {
  Assert( !d_used );

  if(d_nchildren > nchild_thresh) {
    d_children.u_vec = new vector<Node> ();
    d_children.u_vec->reserve(d_nchildren + 5);
    copy(eb.d_children.u_vec->begin(), eb.d_children.u_vec->end(),
         back_inserter(*d_children.u_vec));
  } else {
    ev_iterator j = d_children.u_arr;
    ExprValue* const * i = eb.d_children.u_arr;
    ExprValue* const * i_end = i + eb.d_nchildren;
    for(; i != i_end; ++i, ++j)
      *j = (*i)->inc();
  }
}

NodeBuilder::NodeBuilder(NodeManager* em) :
  d_em(em), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(0) {
}

NodeBuilder::NodeBuilder(NodeManager* em, Kind k) :
  d_em(em), d_kind(k), d_used(false), d_nchildren(0) {
}

NodeBuilder::NodeBuilder(NodeManager* em, const Node& e) :
  d_em(em), d_kind(UNDEFINED_KIND), d_used(false), d_nchildren(1) {
  d_children.u_arr[0] = e.d_ev->inc();
}

NodeBuilder::~NodeBuilder() {
  if(d_nchildren > nchild_thresh) {
    delete d_children.u_vec;
  } else {
    ev_iterator i = d_children.u_arr;
    ev_iterator i_end = d_children.u_arr + d_nchildren;
    for(; i != i_end ; ++i) {
      (*i)->dec();
    }
  }
}

// Compound expression constructors
NodeBuilder& NodeBuilder::eqExpr(const Node& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(EXPECT_TRUE( d_kind != EQUAL )) {
    collapse();
    d_kind = EQUAL;
  }
  addChild(right);
  return *this;
}

NodeBuilder& NodeBuilder::notExpr() {
  Assert( d_kind != UNDEFINED_KIND );
  collapse();
  d_kind = NOT;
  return *this;
}

NodeBuilder& NodeBuilder::andExpr(const Node& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(d_kind != AND) {
    collapse();
    d_kind = AND;
  }
  addChild(right);
  return *this;
}

NodeBuilder& NodeBuilder::orExpr(const Node& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(EXPECT_TRUE( d_kind != OR )) {
    collapse();
    d_kind = OR;
  }
  addChild(right);
  return *this;
}

NodeBuilder& NodeBuilder::iteExpr(const Node& thenpart, const Node& elsepart) {
  Assert( d_kind != UNDEFINED_KIND );
  collapse();
  d_kind = ITE;
  addChild(thenpart);
  addChild(elsepart);
  return *this;
}

NodeBuilder& NodeBuilder::iffExpr(const Node& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(EXPECT_TRUE( d_kind != IFF )) {
    collapse();
    d_kind = IFF;
  }
  addChild(right);
  return *this;
}

NodeBuilder& NodeBuilder::impExpr(const Node& right) {
  Assert( d_kind != UNDEFINED_KIND );
  collapse();
  d_kind = IMPLIES;
  addChild(right);
  return *this;
}

NodeBuilder& NodeBuilder::xorExpr(const Node& right) {
  Assert( d_kind != UNDEFINED_KIND );
  if(EXPECT_TRUE( d_kind != XOR )) {
    collapse();
    d_kind = XOR;
  }
  addChild(right);
  return *this;
}

// "Stream" expression constructor syntax
NodeBuilder& NodeBuilder::operator<<(const Kind& op) {
  d_kind = op;
  return *this;
}

NodeBuilder& NodeBuilder::operator<<(const Node& child) {
  addChild(child);
  return *this;
}

/**
 * We keep the children either:
 * (a) In the array of expression values if the number of children is less than
 *     nchild_thresh. Hence (last else) we increase the reference count.
 * (b) If the number of children reaches the nchild_thresh, we allocate a vector
 *     for the children. Children are now expressions, so we also decrement the
 *     reference count for each child.
 * (c) Otherwise we just add to the end of the vector.
 */
void NodeBuilder::addChild(ExprValue* ev) {
  Assert(d_nchildren <= nchild_thresh ||
         d_nchildren == d_children.u_vec->size(),
         "children count doesn't reflect the size of the vector!");
  Debug("expr") << "adding child ev " << ev << endl;
  if(d_nchildren == nchild_thresh) {
    Debug("expr") << "reached thresh " << nchild_thresh << ", copying" << endl;
    vector<Node>* v = new vector<Node> ();
    v->reserve(nchild_thresh + 5);
    ExprValue** i = d_children.u_arr;
    ExprValue** i_end = i + nchild_thresh;
    for(;i != i_end; ++ i) {
      v->push_back(Node(*i));
      (*i)->dec();
    }
    v->push_back(Node(ev));
    d_children.u_vec = v;
    ++d_nchildren;
  } else if(d_nchildren > nchild_thresh) {
    Debug("expr") << "over thresh " << d_nchildren
                  << " > " << nchild_thresh << endl;
    d_children.u_vec->push_back(Node(ev));
    // ++d_nchildren; no need for this
  } else {
    Debug("expr") << "under thresh " << d_nchildren
                  << " < " << nchild_thresh << endl;
    d_children.u_arr[d_nchildren ++] = ev->inc();
  }
}

NodeBuilder& NodeBuilder::collapse() {
  if(d_nchildren == nchild_thresh) {
    vector<Node>* v = new vector<Node> ();
    v->reserve(nchild_thresh + 5);
    //
    Unreachable();// unimplemented
  }
  return *this;
}

}/* CVC4 namespace */
