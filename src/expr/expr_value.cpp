/*********************                                           -*- C++ -*-  */
/** expr_value.cpp
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
 ** cvc4::Expr rather than by pointer; cvc4::Expr maintains the
 ** reference count on ExprValue instances and
 **/

#include "expr_value.h"

namespace CVC4 {

size_t ExprValue::next_id = 1;

ExprValue::ExprValue() :
  d_id(0), d_rc(MAX_RC), d_kind(NULL_EXPR), d_nchildren(0) {
}

uint64_t ExprValue::hash() const {
  return computeHash<const_iterator>(d_kind, begin(), end());
}

ExprValue* ExprValue::inc() {
  // FIXME multithreading
  if(d_rc < MAX_RC)
    ++d_rc;
  return this;
}

ExprValue* ExprValue::dec() {
  // FIXME multithreading
  if(d_rc < MAX_RC)
    if(--d_rc == 0) {
      // FIXME gc
      return 0;
    }
  return this;
}

ExprValue::iterator ExprValue::begin() {
  return d_children;
}

ExprValue::iterator ExprValue::end() {
  return d_children + d_nchildren;
}

ExprValue::iterator ExprValue::rbegin() {
  return d_children + d_nchildren - 1;
}

ExprValue::iterator ExprValue::rend() {
  return d_children - 1;
}

ExprValue::const_iterator ExprValue::begin() const {
  return d_children;
}

ExprValue::const_iterator ExprValue::end() const {
  return d_children + d_nchildren;
}

ExprValue::const_iterator ExprValue::rbegin() const {
  return d_children + d_nchildren - 1;
}

ExprValue::const_iterator ExprValue::rend() const {
  return d_children - 1;
}

void ExprValue::toString(std::ostream& out) const {
  out << "(" << Kind(d_kind);
  if(d_kind == VARIABLE) {
    out << ":" << this;
  } else {
    for(const_iterator i = begin(); i != end(); ++i) {
      if(i != end())
        out << " ";
      out << *i;
    }
  }
  out << ")";
}

}/* CVC4 namespace */
