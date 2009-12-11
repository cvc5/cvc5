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
 ** cvc4::Node rather than by pointer; cvc4::Node maintains the
 ** reference count on ExprValue instances and
 **/

/* this must be above the check for __CVC4__EXPR__EXPR_VALUE_H */
/* to resolve a circular dependency */
#include "expr/node.h"

#ifndef __CVC4__EXPR__EXPR_VALUE_H
#define __CVC4__EXPR__EXPR_VALUE_H

#include "cvc4_config.h"
#include <stdint.h>
#include "kind.h"

#include <string>

namespace CVC4 {

class Node;
class NodeBuilder;

namespace expr {

/**
 * This is an ExprValue.
 */
class ExprValue {

  /** A convenient null-valued expression value */
  static ExprValue s_null;

  /** Maximum reference count possible.  Used for sticky
   *  reference-counting.  Should be (1 << num_bits(d_rc)) - 1 */
  static const unsigned MAX_RC = 255;

  // this header fits into one 64-bit word

  /** The ID (0 is reserved for the null value) */
  unsigned d_id        : 32;

  /** The expression's reference count.  @see cvc4::Node. */
  unsigned d_rc        :  8;

  /** Kind of the expression */
  unsigned d_kind      :  8;

  /** Number of children */
  unsigned d_nchildren : 16;

  /** Variable number of child nodes */
  Node     d_children[0];

  // todo add exprMgr ref in debug case

  friend class CVC4::Node;
  friend class CVC4::NodeBuilder;

  ExprValue* inc();
  ExprValue* dec();

  static size_t next_id;

  /** Private default constructor for the null value. */
  ExprValue();

  /**
   * Computes the hash over the given iterator span of children, and the
   * root hash. The iterator should be either over a range of Node or pointers
   * to ExprValue.
   * @param hash the initial value for the hash
   * @param begin the begining of the range
   * @param end the end of the range
   * @return the hash value
   */
  template<typename const_iterator_type>
  static uint64_t computeHash(uint64_t hash, const_iterator_type begin, const_iterator_type end) {
    for(const_iterator_type i = begin; i != end; ++i)
      hash = ((hash << 3) | ((hash & 0xE000000000000000ull) >> 61)) ^ (*i)->getId();
    return hash;
  }

public:
  /** Hash this expression.
   *  @return the hash value of this expression. */
  uint64_t hash() const;

  // Iterator support

  typedef Node* iterator;
  typedef Node const* const_iterator;

  iterator begin();
  iterator end();
  iterator rbegin();
  iterator rend();

  const_iterator begin() const;
  const_iterator end() const;
  const_iterator rbegin() const;
  const_iterator rend() const;

  unsigned getId() const { return d_id; }
  unsigned getKind() const { return (Kind) d_kind; }
  std::string toString() const;
  void toStream(std::ostream& out) const;
};

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__EXPR_VALUE_H */
