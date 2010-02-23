/*********************                                                        */
/** node_value.cpp
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
 ** An expression node.
 **
 ** Instances of this class are generally referenced through
 ** cvc4::Node rather than by pointer; cvc4::Node maintains the
 ** reference count on NodeValue instances and
 **/

#include "expr/node_value.h"
#include "expr/node.h"
#include <sstream>

using namespace std;

namespace CVC4 {

size_t NodeValue::next_id = 1;

NodeValue NodeValue::s_null;

NodeValue::NodeValue() :
  d_id(0),
  d_rc(MAX_RC),
  d_kind(NULL_EXPR),
  d_nchildren(0) {
}

NodeValue::NodeValue(int) :
  d_id(0),
  d_rc(0),
  d_kind(kindToDKind(UNDEFINED_KIND)),
  d_nchildren(0) {
}

NodeValue::~NodeValue() {
  for(nv_iterator i = nv_begin(); i != nv_end(); ++i) {
    (*i)->dec();
  }
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

NodeValue::nv_iterator NodeValue::nv_begin() {
  return d_children;
}

NodeValue::nv_iterator NodeValue::nv_end() {
  return d_children + d_nchildren;
}

NodeValue::const_nv_iterator NodeValue::nv_begin() const {
  return d_children;
}

NodeValue::const_nv_iterator NodeValue::nv_end() const {
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
    Node n(this);
    string s;
    if(n.hasAttribute(VarNameAttr(), &s)) {
      out << ":" << s;
    } else {
      out << ":" << this;
    }
  } else {
    for(const_nv_iterator i = nv_begin(); i != nv_end(); ++i) {
      if(i != nv_end()) {
        out << " ";
      }
      out << *i;
    }
  }
  out << ")";
}

}/* CVC4 namespace */
