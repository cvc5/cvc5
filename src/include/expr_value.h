/*********************
/** expr_value.h
 ** This file is part of the CVC4 prototype.
 **
 ** An expression node.
 **
 ** Instances of this class are generally referenced through
 ** cvc4::Expr rather than by pointer; cvc4::Expr maintains the
 ** reference count on ExprValue instances and
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 **/

#ifndef __CVC4_EXPR_VALUE_H
#define __CVC4_EXPR_VALUE_H

#include <stdint.h>
#include "expr.h"

namespace CVC4 {

/**
 * This is an ExprValue.
 */
class ExprValue {
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

  friend class Expr;

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

} /* CVC4 namespace */

#endif /* __CVC4_EXPR_VALUE_H */
