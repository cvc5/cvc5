/*********************                                                        */
/** node_value.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): none
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

/* this must be above the check for __CVC4__EXPR__NODE_VALUE_H */
/* to resolve a circular dependency */
//#include "expr/node.h"

#ifndef __CVC4__EXPR__NODE_VALUE_H
#define __CVC4__EXPR__NODE_VALUE_H

#include "cvc4_config.h"
#include <stdint.h>
#include "kind.h"

#include <string>
#include <iterator>

namespace CVC4 {

class Node;
template <unsigned> class NodeBuilder;
class NodeManager;

namespace expr {

/**
 * This is an NodeValue.
 */
class NodeValue {

  /** A convenient null-valued expression value */
  static NodeValue s_null;

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
  NodeValue *d_children[0];

  // todo add exprMgr ref in debug case

  friend class CVC4::Node;
  template <unsigned> friend class CVC4::NodeBuilder;
  friend class CVC4::NodeManager;

  void inc();
  void dec();

  static size_t next_id;

  /** Private default constructor for the null value. */
  NodeValue();

  /** Private default constructor for the NodeBuilder. */
  NodeValue(int);

  /** Destructor decrements the ref counts of its children */
  ~NodeValue();

  /**
   * Computes the hash over the given iterator span of children, and the
   * root hash. The iterator should be either over a range of Node or pointers
   * to NodeValue.
   * @param hash the initial value for the hash
   * @param begin the begining of the range
   * @param end the end of the range
   * @return the hash value
   */
  template<typename const_iterator_type>
  static uint64_t computeHash(uint64_t hash, const_iterator_type begin,
                              const_iterator_type end) {
    for(const_iterator_type i = begin; i != end; ++i) {
      hash = computeHash(hash, *i);
    }
    return hash;
  }

  static uint64_t computeHash(uint64_t hash, const NodeValue* ev) {
    return
      ( (hash << 3) | ((hash & 0xE000000000000000ull) >> 61) ) ^ ev->getId();
  }

  typedef NodeValue** ev_iterator;
  typedef NodeValue const* const* const_ev_iterator;

  ev_iterator ev_begin();
  ev_iterator ev_end();

  const_ev_iterator ev_begin() const;
  const_ev_iterator ev_end() const;

  class node_iterator {
    const_ev_iterator d_i;
  public:
    explicit node_iterator(const_ev_iterator i) : d_i(i) {}

    inline Node operator*();

    bool operator==(const node_iterator& i) {
      return d_i == i.d_i;
    }

    bool operator!=(const node_iterator& i) {
      return d_i != i.d_i;
    }

    node_iterator operator++() {
      ++d_i;
      return *this;
    }

    node_iterator operator++(int) {
      return node_iterator(d_i++);
    }

    typedef std::input_iterator_tag iterator_category;
    typedef Node value_type;
    typedef ptrdiff_t difference_type;
    typedef Node* pointer;
    typedef Node& reference;
  };
  typedef node_iterator const_node_iterator;

public:
  /** Hash this expression.
   *  @return the hash value of this expression. */
  uint64_t hash() const;

  // Iterator support

  typedef node_iterator iterator;
  typedef node_iterator const_iterator;

  iterator begin();
  iterator end();

  const_iterator begin() const;
  const_iterator end() const;

  unsigned getId() const { return d_id; }
  Kind getKind() const { return (Kind) d_kind; }
  unsigned getNumChildren() const { return d_nchildren; }

  std::string toString() const;
  void toStream(std::ostream& out) const;
};

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#include "expr/node.h"

namespace CVC4 {
namespace expr {

inline Node NodeValue::node_iterator::operator*() {
  return Node(*d_i);
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__NODE_VALUE_H */
