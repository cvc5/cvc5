/*********************                                           -*- C++ -*-  */
/** expr_value.h
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

/* this must be above the check for __CVC4__EXPR__EXPR_VALUE_H */
/* to resolve a circular dependency */
#include "cvc4_expr.h"

#ifndef __CVC4__EXPR__EXPR_VALUE_H
#define __CVC4__EXPR__EXPR_VALUE_H

#include <stdint.h>

namespace CVC4 {

class Expr;
class ExprBuilder;

namespace expr {

/**
 * This is an ExprValue.
 */
class ExprValue {
  /** Maximum reference count possible.  Used for sticky
   *  reference-counting.  Should be (1 << num_bits(d_rc)) - 1 */
  static const unsigned MAX_RC = 255;

  // this header fits into one 64-bit word

  /** The ID */
  unsigned d_id        : 32;

  /** The expression's reference count.  @see cvc4::Expr. */
  unsigned d_rc        :  8;

  /** Kind of the expression */
  unsigned d_kind      :  8;

  /** Number of children */
  unsigned d_nchildren : 16;

  /** Variable number of child nodes */
  Expr     d_children[0];

  // todo add exprMgr ref in debug case

  friend class CVC4::Expr;
  friend class CVC4::ExprBuilder;

  ExprValue* inc();
  ExprValue* dec();

public:
  /** Hash this expression.
   *  @return the hash value of this expression. */
  uint64_t hash() const;

  // Iterator support

  typedef Expr* iterator;
  typedef Expr const* const_iterator;

  iterator begin();
  iterator end();
  iterator rbegin();
  iterator rend();

  const_iterator begin() const;
  const_iterator end() const;
  const_iterator rbegin() const;
  const_iterator rend() const;
};

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__EXPR_VALUE_H */
