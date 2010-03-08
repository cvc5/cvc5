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

#include "cvc4_private.h"

#ifndef __CVC4__EXPR__NODE_VALUE_H
#define __CVC4__EXPR__NODE_VALUE_H

#include "cvc4_config.h"
#include <stdint.h>
#include "expr/kind.h"

#include <string>
#include <iterator>

namespace CVC4 {

template <bool ref_count> class NodeTemplate;
template <class Builder> class NodeBuilderBase;
template <unsigned N> class NodeBuilder;
class AndNodeBuilder;
class OrNodeBuilder;
class PlusNodeBuilder;
class MultNodeBuilder;
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

  /** Number of bits assigned to the kind in the NodeValue header */
  static const unsigned KINDBITS = 8;

  /** A mask for d_kind */
  static const unsigned kindMask = (1u << KINDBITS) - 1;

  // this header fits into one 64-bit word

  /** The ID (0 is reserved for the null value) */
  unsigned d_id        : 32;

  /** The expression's reference count.  @see cvc4::Node. */
  unsigned d_rc        :  8;

  /** Kind of the expression */
  unsigned d_kind      : KINDBITS;

  /** Number of children */
  unsigned d_nchildren : 16;

  /** Variable number of child nodes */
  NodeValue *d_children[0];

  // todo add exprMgr ref in debug case

  template <bool> friend class CVC4::NodeTemplate;
  template <class Builder> friend class CVC4::NodeBuilderBase;
  template <unsigned N> friend class CVC4::NodeBuilder;
  friend class CVC4::AndNodeBuilder;
  friend class CVC4::OrNodeBuilder;
  friend class CVC4::PlusNodeBuilder;
  friend class CVC4::MultNodeBuilder;
  friend class CVC4::NodeManager;

  void inc();
  void dec();

  static size_t next_id;

  /** Private default constructor for the null value. */
  NodeValue();

  /** Destructor decrements the ref counts of its children */
  ~NodeValue();

  typedef NodeValue** nv_iterator;
  typedef NodeValue const* const* const_nv_iterator;

  nv_iterator nv_begin();
  nv_iterator nv_end();

  const_nv_iterator nv_begin() const;
  const_nv_iterator nv_end() const;

  template <bool ref_count>
  class iterator {
    const_nv_iterator d_i;
  public:
    explicit iterator(const_nv_iterator i) : d_i(i) {}

    inline CVC4::NodeTemplate<ref_count> operator*();

    bool operator==(const iterator& i) {
      return d_i == i.d_i;
    }

    bool operator!=(const iterator& i) {
      return d_i != i.d_i;
    }

    iterator operator++() {
      ++d_i;
      return *this;
    }

    iterator operator++(int) {
      return iterator(d_i++);
    }

    typedef std::input_iterator_tag iterator_category;
  };

public:

  template <bool ref_count>
  iterator<ref_count> begin() const {
    return iterator<ref_count>(d_children);
  }

  template <bool ref_count>
  iterator<ref_count> end() const {
    return iterator<ref_count>(d_children + d_nchildren);
  }

  /**
   * Hash this NodeValue.  For hash_maps, hash_sets, etc.. but this is
   * for expr package internal use only at present!  This is likely to
   * be POORLY PERFORMING for other uses!  For example, this gives
   * collisions for all VARIABLEs.
   * @return the hash value of this expression.
   */
  size_t internalHash() const {
    size_t hash = d_kind;
    const_nv_iterator i = nv_begin();
    const_nv_iterator i_end = nv_end();
    while(i != i_end) {
      hash ^= (*i)->d_id + 0x9e3779b9 + (hash << 6) + (hash >> 2);
      ++i;
    }
    return hash;
  }

  inline bool compareTo(const NodeValue* nv) const {
    if(d_kind != nv->d_kind) {
      return false;
    }

    if(d_nchildren != nv->d_nchildren) {
      return false;
    }

    const_nv_iterator i = nv_begin();
    const_nv_iterator j = nv->nv_begin();
    const_nv_iterator i_end = nv_end();

    while(i != i_end) {
      if((*i) != (*j)) {
        return false;
      }
      ++i;
      ++j;
    }

    return true;
  }

  // Comparison predicate
  struct NodeValueEq {
    bool operator()(const NodeValue* nv1, const NodeValue* nv2) const {
      return nv1->compareTo(nv2);
    }
  };

  unsigned getId() const { return d_id; }
  Kind getKind() const { return dKindToKind(d_kind); }
  unsigned getNumChildren() const { return d_nchildren; }

  std::string toString() const;
  void toStream(std::ostream& out) const;

  static inline unsigned kindToDKind(Kind k) {
    return ((unsigned) k) & kindMask;
  }

  static inline Kind dKindToKind(unsigned d) {
    return (d == kindMask) ? kind::UNDEFINED_KIND : Kind(d);
  }
};/* class NodeValue */

/**
 * For hash_maps, hash_sets, etc.. but this is for expr package
 * internal use only at present!  This is likely to be POORLY
 * PERFORMING for other uses!  NodeValue::internalHash() will lead to
 * collisions for all VARIABLEs.
 */
struct NodeValueInternalHashFcn {
  inline size_t operator()(const NodeValue* nv) const {
    return (size_t) nv->internalHash();
  }
};/* struct NodeValueHashFcn */

/**
 * For hash_maps, hash_sets, etc.
 */
struct NodeValueIDHashFcn {
  inline size_t operator()(const NodeValue* nv) const {
    return (size_t) nv->getId();
  }
};/* struct NodeValueHashFcn */

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#include "node_manager.h"

namespace CVC4 {
namespace expr {

inline NodeValue::NodeValue() :
  d_id(0),
  d_rc(MAX_RC),
  d_kind(kind::NULL_EXPR),
  d_nchildren(0) {
}

inline NodeValue::~NodeValue() {
  for(nv_iterator i = nv_begin(); i != nv_end(); ++i) {
    (*i)->dec();
  }
}

inline void NodeValue::inc() {
  // FIXME multithreading
  if(EXPECT_TRUE( d_rc < MAX_RC )) {
    ++d_rc;
  }
}

inline void NodeValue::dec() {
  // FIXME multithreading
  if(EXPECT_TRUE( d_rc < MAX_RC )) {
    --d_rc;
    if(EXPECT_FALSE( d_rc == 0 )) {
      Assert(NodeManager::currentNM() != NULL,
             "No current NodeManager on destruction of NodeValue: "
             "maybe a public CVC4 interface function is missing a NodeManagerScope ?");
      NodeManager::currentNM()->gc(this);
    }
  }
}

inline NodeValue::nv_iterator NodeValue::nv_begin() {
  return d_children;
}

inline NodeValue::nv_iterator NodeValue::nv_end() {
  return d_children + d_nchildren;
}

inline NodeValue::const_nv_iterator NodeValue::nv_begin() const {
  return d_children;
}

inline NodeValue::const_nv_iterator NodeValue::nv_end() const {
  return d_children + d_nchildren;
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#include "expr/node.h"

namespace CVC4 {
namespace expr {

template <bool ref_count>
inline CVC4::NodeTemplate<ref_count> NodeValue::iterator<ref_count>::operator*() {
  return NodeTemplate<ref_count>(*d_i);
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__NODE_VALUE_H */
