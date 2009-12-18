/*********************                                           -*- C++ -*-  */
/** node_value.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** An expression node.
 **
 ** Instances of this class are generally referenced through
 ** cvc4::Node rather than by pointer; cvc4::Node maintains the
 ** reference count on NodeValue instances and
 **/

#include "node_value.h"
#include <sstream>

using namespace std;

namespace CVC4 {

size_t NodeValue::next_id = 1;

NodeValue::NodeValue() :
  d_id(0), d_rc(MAX_RC), d_kind(NULL_EXPR), d_nchildren(0) {
}

NodeValue::NodeValue(int) :
  d_id(0), d_rc(0), d_kind(unsigned(UNDEFINED_KIND)), d_nchildren(0) {
}

NodeValue::~NodeValue() {
  for(ev_iterator i = ev_begin(); i != ev_end(); ++i) {
    (*i)->dec();
  }
}

uint64_t NodeValue::hash() const {
  return computeHash(d_kind, ev_begin(), ev_end());
}

void NodeValue::inc() {
  // FIXME multithreading
  if(EXPECT_TRUE( d_rc < MAX_RC )) {
    ++d_rc;
  }
}

void NodeValue::dec() {
  // FIXME multithreading
  if(EXPECT_TRUE( d_rc < MAX_RC )) {
    --d_rc;
    if(EXPECT_FALSE( d_rc == 0 )) {
      // FIXME gc
    }
  }
}

NodeValue::iterator NodeValue::begin() {
  return node_iterator(d_children);
}

NodeValue::iterator NodeValue::end() {
  return node_iterator(d_children + d_nchildren);
}

NodeValue::const_iterator NodeValue::begin() const {
  return const_node_iterator(d_children);
}

NodeValue::const_iterator NodeValue::end() const {
  return const_node_iterator(d_children + d_nchildren);
}

NodeValue::ev_iterator NodeValue::ev_begin() {
  return d_children;
}

NodeValue::ev_iterator NodeValue::ev_end() {
  return d_children + d_nchildren;
}

NodeValue::const_ev_iterator NodeValue::ev_begin() const {
  return d_children;
}

NodeValue::const_ev_iterator NodeValue::ev_end() const {
  return d_children + d_nchildren;
}

string NodeValue::toString() const {
  stringstream ss;
  toStream(ss);
  return ss.str();
}

void NodeValue::toStream(std::ostream& out) const {
  out << "(" << Kind(d_kind);
  if(d_kind == VARIABLE) {
    out << ":" << this;
  } else {
    for(const_ev_iterator i = ev_begin(); i != ev_end(); ++i) {
      if(i != ev_end()) {
        out << " ";
      }
      out << *i;
    }
  }
  out << ")";
}

}/* CVC4 namespace */
