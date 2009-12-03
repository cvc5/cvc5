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

size_t ExprValue::next_id = 0;

uint64_t ExprValue::hash() const {
  uint64_t hash = d_kind;

  for(const_iterator i = begin(); i != end(); ++i)
    hash = ((hash << 3) | ((hash & 0xE000000000000000ull) >> 61)) ^ i->hash();

  return hash;
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

}/* CVC4 namespace */
