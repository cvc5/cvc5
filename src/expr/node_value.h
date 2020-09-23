/*********************                                                        */
/*! \file node_value.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Aina Niemetz, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief An expression node.
 **
 ** An expression node.
 **
 ** Instances of this class are generally referenced through
 ** cvc4::Node rather than by pointer; cvc4::Node maintains the
 ** reference count on NodeValue instances and
 **/

#include "cvc4_private.h"

// circular dependency
#include "expr/metakind.h"

#ifndef CVC4__EXPR__NODE_VALUE_H
#define CVC4__EXPR__NODE_VALUE_H

#include <stdint.h>

#include <iterator>
#include <string>

#include "expr/kind.h"
#include "options/language.h"

namespace CVC4 {

template <bool ref_count> class NodeTemplate;
class TypeNode;
template <unsigned N> class NodeBuilder;
class NodeManager;

namespace expr {
  class NodeValue;
}

namespace kind {
  namespace metakind {
    template < ::CVC4::Kind k, bool pool >
    struct NodeValueConstCompare;

    struct NodeValueCompare;
    struct NodeValueConstPrinter;

    void deleteNodeValueConstant(::CVC4::expr::NodeValue* nv);
  }/* CVC4::kind::metakind namespace */
}/* CVC4::kind namespace */

namespace expr {

/**
 * This is a NodeValue.
 */
class NodeValue
{
  template <bool>
  friend class ::CVC4::NodeTemplate;
  friend class ::CVC4::TypeNode;
  template <unsigned nchild_thresh>
  friend class ::CVC4::NodeBuilder;
  friend class ::CVC4::NodeManager;

  template <Kind k, bool pool>
  friend struct ::CVC4::kind::metakind::NodeValueConstCompare;

  friend struct ::CVC4::kind::metakind::NodeValueCompare;
  friend struct ::CVC4::kind::metakind::NodeValueConstPrinter;

  friend void ::CVC4::kind::metakind::deleteNodeValueConstant(NodeValue* nv);

  friend class RefCountGuard;

  /* ------------------------------------------------------------------------ */
 public:
  /* ------------------------------------------------------------------------ */

  using nv_iterator = NodeValue**;
  using const_nv_iterator = NodeValue const* const*;

  template <class T>
  class iterator
  {
   public:
    using iterator_category = std::random_access_iterator_tag;
    using value_type = T;
    using difference_type = std::ptrdiff_t;
    using pointer = T*;
    using reference = T&;

    iterator() : d_i(NULL) {}
    explicit iterator(const_nv_iterator i) : d_i(i) {}

    /** Conversion of a TNode iterator to a Node iterator. */
    inline operator NodeValue::iterator<NodeTemplate<true> >()
    {
      return iterator<NodeTemplate<true> >(d_i);
    }

    inline T operator*() const;

    bool operator==(const iterator& i) const { return d_i == i.d_i; }

    bool operator!=(const iterator& i) const { return d_i != i.d_i; }

    iterator& operator++()
    {
      ++d_i;
      return *this;
    }

    iterator operator++(int) { return iterator(d_i++); }

    iterator& operator--()
    {
      --d_i;
      return *this;
    }

    iterator operator--(int) { return iterator(d_i--); }

    iterator& operator+=(difference_type p)
    {
      d_i += p;
      return *this;
    }

    iterator& operator-=(difference_type p)
    {
      d_i -= p;
      return *this;
    }

    iterator operator+(difference_type p) { return iterator(d_i + p); }

    iterator operator-(difference_type p) { return iterator(d_i - p); }

    difference_type operator-(iterator i) { return d_i - i.d_i; }

   private:
    const_nv_iterator d_i;

  }; /* class NodeValue::iterator<T> */

  uint64_t getId() const { return d_id; }

  Kind getKind() const { return dKindToKind(d_kind); }

  kind::MetaKind getMetaKind() const { return kind::metaKindOf(getKind()); }

  uint32_t getNumChildren() const
  {
    return (getMetaKind() == kind::metakind::PARAMETERIZED) ? d_nchildren - 1
                                                            : d_nchildren;
  }

  /* ------------------------------ Header ---------------------------------- */
  /** Number of bits reserved for reference counting. */
  static constexpr uint32_t NBITS_REFCOUNT = 20;
  /** Number of bits reserved for node kind. */
  static constexpr uint32_t NBITS_KIND = 10;
  /** Number of bits reserved for node id. */
  static constexpr uint32_t NBITS_ID = 40;
  /** Number of bits reserved for number of children. */
  static const uint32_t NBITS_NCHILDREN = 26;
  static_assert(NBITS_REFCOUNT + NBITS_KIND + NBITS_ID + NBITS_NCHILDREN == 96,
                "NodeValue header bit assignment does not sum to 96 !");
  /* ------------------- This header fits into 96 bits ---------------------- */

  /** Maximum number of children possible. */
  static constexpr uint32_t MAX_CHILDREN =
      (static_cast<uint32_t>(1) << NBITS_NCHILDREN) - 1;

  uint32_t getRefCount() const { return d_rc; }

  NodeValue* getOperator() const;
  NodeValue* getChild(int i) const;

  /** If this is a CONST_* Node, extract the constant from it.  */
  template <class T>
  inline const T& getConst() const;

  static inline NodeValue& null()
  {
    static NodeValue* s_null = new NodeValue(0);
    return *s_null;
  }

  /**
   * Hash this NodeValue.  For hash_maps, hash_sets, etc.. but this is
   * for expr package internal use only at present!  This is likely to
   * be POORLY PERFORMING for other uses!  For example, this gives
   * collisions for all VARIABLEs.
   * @return the hash value of this expression.
   */
  size_t poolHash() const
  {
    if (getMetaKind() == kind::metakind::CONSTANT)
    {
      return kind::metakind::NodeValueCompare::constHash(this);
    }

    size_t hash = d_kind;
    const_nv_iterator i = nv_begin();
    const_nv_iterator i_end = nv_end();
    while (i != i_end)
    {
      hash ^= (*i)->d_id + 0x9e3779b9 + (hash << 6) + (hash >> 2);
      ++i;
    }
    return hash;
  }

  static inline uint32_t kindToDKind(Kind k)
  {
    return ((uint32_t)k) & kindMask;
  }

  static inline Kind dKindToKind(uint32_t d)
  {
    return (d == kindMask) ? kind::UNDEFINED_KIND : Kind(d);
  }

  std::string toString() const;

  void toStream(std::ostream& out,
                int toDepth = -1,
                bool types = false,
                size_t dag = 1,
                OutputLanguage = language::output::LANG_AUTO) const;

  void printAst(std::ostream& out, int indent = 0) const;

  template <typename T>
  inline iterator<T> begin() const;
  template <typename T>
  inline iterator<T> end() const;

  /* ------------------------------------------------------------------------ */
 private:
  /* ------------------------------------------------------------------------ */

  /**
   * RAII guard that increases the reference count if the reference count to be
   * > 0.  Otherwise, this does nothing. This does not just increment the
   * reference count to avoid maxing out the d_rc field. This is only for low
   * level functions.
   */
  class RefCountGuard
  {
   public:
    RefCountGuard(const NodeValue* nv) : d_nv(const_cast<NodeValue*>(nv))
    {
      d_increased = (d_nv->d_rc == 0);
      if (d_increased)
      {
        d_nv->d_rc = 1;
      }
    }
    ~RefCountGuard()
    {
      // dec() without marking for deletion: we don't want to garbage
      // collect this NodeValue if ours is the last reference to it.
      // E.g., this can happen when debugging code calls the print
      // routines below.  As RefCountGuards are scoped on the stack,
      // this should be fine---but not in multithreaded contexts!
      if (d_increased)
      {
        --d_nv->d_rc;
      }
    }

   private:
    NodeValue* d_nv;
    bool d_increased;
  }; /* NodeValue::RefCountGuard */

  /** Maximum reference count possible.  Used for sticky
   *  reference-counting.  Should be (1 << num_bits(d_rc)) - 1 */
  static constexpr uint32_t MAX_RC =
      (static_cast<uint32_t>(1) << NBITS_REFCOUNT) - 1;

  /** A mask for d_kind */
  static constexpr uint32_t kindMask =
      (static_cast<uint32_t>(1) << NBITS_KIND) - 1;

  /** Uninitializing constructor for NodeBuilder's use.  */
  NodeValue()
  { /* do not initialize! */
  }
  /** Private constructor for the null value. */
  NodeValue(int);

  void inc();
  void dec();

  /** Decrement ref counts of children */
  inline void decrRefCounts();

  bool isBeingDeleted() const;

  /** Returns true if the reference count is maximized. */
  inline bool HasMaximizedReferenceCount() { return d_rc == MAX_RC; }

  nv_iterator nv_begin();
  nv_iterator nv_end();

  const_nv_iterator nv_begin() const;
  const_nv_iterator nv_end() const;

  /**
   * Indents the given stream a given amount of spaces.
   * @param out the stream to indent
   * @param indent the numer of spaces
   */
  static inline void indent(std::ostream& out, int indent)
  {
    for (int i = 0; i < indent; i++)
    {
      out << ' ';
    }
  }

  /** The ID (0 is reserved for the null value) */
  uint64_t d_id : NBITS_ID;

  /** The expression's reference count.  @see cvc4::Node. */
  uint32_t d_rc : NBITS_REFCOUNT;

  /** Kind of the expression */
  uint32_t d_kind : NBITS_KIND;

  /** Number of children */
  uint32_t d_nchildren : NBITS_NCHILDREN;

  /** Variable number of child nodes */
  NodeValue* d_children[0];
}; /* class NodeValue */

/**
 * Provides a symmetric addition operator to that already defined in
 * the iterator class.
 */
NodeValue::iterator<NodeTemplate<true> > operator+(
    NodeValue::iterator<NodeTemplate<true> >::difference_type p,
    NodeValue::iterator<NodeTemplate<true> > i);

/**
 * Provides a symmetric addition operator to that already defined in
 * the iterator class.
 */
NodeValue::iterator<NodeTemplate<false> > operator+(
    NodeValue::iterator<NodeTemplate<false> >::difference_type p,
    NodeValue::iterator<NodeTemplate<false> > i);

/**
 * For hash_maps, hash_sets, etc.. but this is for expr package
 * internal use only at present!  This is likely to be POORLY
 * PERFORMING for other uses!  NodeValue::poolHash() will lead to
 * collisions for all VARIABLEs.
 */
struct NodeValuePoolHashFunction {
  inline size_t operator()(const NodeValue* nv) const {
    return (size_t) nv->poolHash();
  }
};/* struct NodeValuePoolHashFunction */

/**
 * For hash_maps, hash_sets, etc.
 */
struct NodeValueIDHashFunction {
  inline size_t operator()(const NodeValue* nv) const {
    return (size_t) nv->getId();
  }
};/* struct NodeValueIDHashFunction */


/**
 * An equality predicate that is applicable between pointers to fully
 * constructed NodeValues.
 */
struct NodeValueIDEquality {
  inline bool operator()(const NodeValue* a, const NodeValue* b) const {
    return a->getId() == b->getId();
  }
};


inline std::ostream& operator<<(std::ostream& out, const NodeValue& nv);

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#include "expr/node_manager.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace expr {

inline NodeValue::NodeValue(int) :
  d_id(0),
  d_rc(MAX_RC),
  d_kind(kind::NULL_EXPR),
  d_nchildren(0) {
}

inline void NodeValue::decrRefCounts() {
  for(nv_iterator i = nv_begin(); i != nv_end(); ++i) {
    (*i)->dec();
  }
}

inline void NodeValue::inc() {
  Assert(!isBeingDeleted())
      << "NodeValue is currently being deleted "
         "and increment is being called on it. Don't Do That!";
  // FIXME multithreading
  if (__builtin_expect((d_rc < MAX_RC - 1), true)) {
    ++d_rc;
  } else if (__builtin_expect((d_rc == MAX_RC - 1), false)) {
    ++d_rc;
    Assert(NodeManager::currentNM() != NULL)
        << "No current NodeManager on incrementing of NodeValue: "
           "maybe a public CVC4 interface function is missing a "
           "NodeManagerScope ?";
    NodeManager::currentNM()->markRefCountMaxedOut(this);
  }
}

inline void NodeValue::dec() {
  // FIXME multithreading
  if(__builtin_expect( ( d_rc < MAX_RC ), true )) {
    --d_rc;
    if(__builtin_expect( ( d_rc == 0 ), false )) {
      Assert(NodeManager::currentNM() != NULL)
          << "No current NodeManager on destruction of NodeValue: "
             "maybe a public CVC4 interface function is missing a "
             "NodeManagerScope ?";
      NodeManager::currentNM()->markForDeletion(this);
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

template <typename T>
inline NodeValue::iterator<T> NodeValue::begin() const {
  NodeValue* const* firstChild = d_children;
  if(getMetaKind() == kind::metakind::PARAMETERIZED) {
    ++firstChild;
  }
  return iterator<T>(firstChild);
}

template <typename T>
inline NodeValue::iterator<T> NodeValue::end() const {
  return iterator<T>(d_children + d_nchildren);
}

inline bool NodeValue::isBeingDeleted() const {
  return NodeManager::currentNM() != NULL &&
    NodeManager::currentNM()->isCurrentlyDeleting(this);
}

inline NodeValue* NodeValue::getOperator() const {
  Assert(getMetaKind() == kind::metakind::PARAMETERIZED);
  return d_children[0];
}

inline NodeValue* NodeValue::getChild(int i) const {
  if(getMetaKind() == kind::metakind::PARAMETERIZED) {
    ++i;
  }

  Assert(i >= 0 && unsigned(i) < d_nchildren);
  return d_children[i];
}

}/* CVC4::expr namespace */
}/* CVC4 namespace */

#include "expr/node.h"
#include "expr/type_node.h"

namespace CVC4 {
namespace expr {

template <typename T>
inline T NodeValue::iterator<T>::operator*() const {
  return T(*d_i);
}

inline std::ostream& operator<<(std::ostream& out, const NodeValue& nv) {
  nv.toStream(out,
              Node::setdepth::getDepth(out),
              Node::printtypes::getPrintTypes(out),
              Node::dag::getDag(out),
              Node::setlanguage::getLanguage(out));
  return out;
}

}/* CVC4::expr namespace */

#ifdef CVC4_DEBUG
/**
 * Pretty printer for use within gdb.  This is not intended to be used
 * outside of gdb.  This writes to the Warning() stream and immediately
 * flushes the stream.
 */
static void __attribute__((used)) debugPrintNodeValue(const expr::NodeValue* nv) {
  Warning() << Node::setdepth(-1)
            << Node::printtypes(false)
            << Node::dag(true)
            << Node::setlanguage(language::output::LANG_AST)
            << *nv << std::endl;
  Warning().flush();
}
static void __attribute__((used)) debugPrintNodeValueNoDag(const expr::NodeValue* nv) {
  Warning() << Node::setdepth(-1)
            << Node::printtypes(false)
            << Node::dag(false)
            << Node::setlanguage(language::output::LANG_AST)
            << *nv << std::endl;
  Warning().flush();
}
static void __attribute__((used)) debugPrintRawNodeValue(const expr::NodeValue* nv) {
  nv->printAst(Warning(), 0);
  Warning().flush();
}
#endif /* CVC4_DEBUG */

}/* CVC4 namespace */

#endif /* CVC4__EXPR__NODE_VALUE_H */
