/*********************                                                        */
/*! \file node_builder.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A builder interface for Nodes.
 **
 ** A builder interface for Nodes.
 **
 ** The idea is to permit a flexible and efficient (in the common
 ** case) interface for building Nodes.  The general pattern of use is
 ** to create a NodeBuilder, set its kind, append children to it, then
 ** "extract" the resulting Node.  This resulting Node may be one that
 ** already exists (the NodeManager keeps a table of all Nodes in the
 ** system), or may be entirely new.
 **
 ** This implementation gets a bit hairy for a handful of reasons.  We
 ** want a user-supplied "in-line" buffer (probably on the stack, see
 ** below) to hold the children, but then the number of children must
 ** be known ahead of time.  Therefore, if this buffer is overrun, we
 ** need to heap-allocate a new buffer to hold the children.
 **
 ** Note that as children are added to a NodeBuilder, they are stored
 ** as raw pointers-to-NodeValue.  However, their reference counts are
 ** carefully maintained.
 **
 ** When the "in-line" buffer "d_inlineNv" is superceded by a
 ** heap-allocated buffer, we allocate the new buffer (a NodeValue
 ** large enough to hold more children), copy the elements to it, and
 ** mark d_inlineNv as having zero children.  We do this last bit so
 ** that we don't have to modify any child reference counts.  The new
 ** heap-allocated buffer "takes over" the reference counts of the old
 ** "in-line" buffer.  (If we didn't mark it as having zero children,
 ** the destructor may improperly decrement the children's reference
 ** counts.)
 **
 ** There are then four normal cases at the end of a NodeBuilder's
 ** life cycle:
 **
 **   0. We have a VARIABLE-kinded Node.  These are special (they have
 **      no children and are all distinct by definition).  They are
 **      really a subcase of 1(b), below.
 **   1. d_nv points to d_inlineNv: it is the backing store supplied
 **      by the user (or derived class).
 **      (a) The Node under construction already exists in the
 **          NodeManager's pool.
 **      (b) The Node under construction is NOT already in the
 **          NodeManager's pool.
 **   2. d_nv does NOT point to d_inlineNv: it is a new, larger buffer
 **      that was heap-allocated by this NodeBuilder.
 **      (a) The Node under construction already exists in the
 **          NodeManager's pool.
 **      (b) The Node under construction is NOT already in the
 **          NodeManager's pool.
 **
 ** When a Node is extracted, we convert the NodeBuilder to a Node and
 ** make sure the reference counts are properly maintained.  That
 ** means we must ensure there are no reference-counting errors among
 ** the node's children, that the children aren't re-decremented on
 ** clear() or NodeBuilder destruction, and that the returned Node
 ** wraps a NodeValue with a reference count of 1.
 **
 **   0.    If a VARIABLE, treat similarly to 1(b), except that we
 **         know there are no children (no reference counts to reason
 **         about) and we don't keep VARIABLE-kinded Nodes in the
 **         NodeManager pool.
 **
 **   1(a). Reference-counts for all children in d_inlineNv must be
 **         decremented, and the NodeBuilder must be marked as "used"
 **         and the number of children set to zero so that we don't
 **         decrement them again on destruction.  The existing
 **         NodeManager pool entry is returned.
 **
 **   1(b). A new heap-allocated NodeValue must be constructed and all
 **         settings and children from d_inlineNv copied into it.
 **         This new NodeValue is put into the NodeManager's pool.
 **         The NodeBuilder is marked as "used" and the number of
 **         children in d_inlineNv set to zero so that we don't
 **         decrement child reference counts on destruction (the child
 **         reference counts have been "taken over" by the new
 **         NodeValue).  We return a Node wrapper for this new
 **         NodeValue, which increments its reference count.
 **
 **   2(a). Reference counts for all children in d_nv must be
 **         decremented.  The NodeBuilder is marked as "used" and the
 **         heap-allocated d_nv deleted.  d_nv is repointed to
 **         d_inlineNv so that destruction of the NodeBuilder doesn't
 **         cause any problems.  The existing NodeManager pool entry
 **         is returned.
 **
 **   2(b). The heap-allocated d_nv is "cropped" to the correct size
 **         (based on the number of children it _actually_ has).  d_nv
 **         is repointed to d_inlineNv so that destruction of the
 **         NodeBuilder doesn't cause any problems, and the (old)
 **         value it had is placed into the NodeManager's pool and
 **         returned in a Node wrapper.
 **
 ** NOTE IN 1(b) AND 2(b) THAT we can NOT create Node wrapper
 ** temporary for the NodeValue in the NodeBuilder<>::operator Node()
 ** member function.  If we create a temporary (for example by writing
 ** Debug("builder") << Node(nv) << endl), the NodeValue will have its
 ** reference count incremented from zero to one, then decremented,
 ** which makes it eligible for collection before the builder has even
 ** returned it!  So this is a no-no.
 **
 ** There are also two cases when the NodeBuilder is clear()'ed:
 **
 **   1. d_nv == &d_inlineNv (NodeBuilder using the user-supplied
 **      backing store): all d_inlineNv children have their reference
 **      counts decremented, d_inlineNv.d_nchildren is set to zero,
 **      and its kind is set to UNDEFINED_KIND.
 **
 **   2. d_nv != &d_inlineNv (d_nv heap-allocated by NodeBuilder): all
 **      d_nv children have their reference counts decremented, d_nv
 **      is deallocated, and d_nv is set to &d_inlineNv.  d_inlineNv's
 **      kind is set to UNDEFINED_KIND.
 **
 ** ... destruction is similar:
 **
 **   1. d_nv == &d_inlineNv (NodeBuilder using the user-supplied
 **      backing store): all d_inlineNv children have their reference
 **      counts decremented.
 **
 **   2. d_nv != &d_inlineNv (d_nv heap-allocated by NodeBuilder): all
 **      d_nv children have their reference counts decremented, and
 **      d_nv is deallocated.
 **
 ** Regarding the backing store (typically on the stack): the file
 ** below provides the template:
 **
 **   template < unsigned nchild_thresh > class NodeBuilder;
 **
 **     The default:
 **
 **       NodeBuilder<> b;
 **
 **     gives you a backing buffer with capacity for 10 children in
 **     the same place as the NodeBuilder<> itself is allocated.  You
 **     can specify another size as a template parameter, but it must
 **     be a compile-time constant.
 **/

#include "cvc4_private.h"

/* strong dependency; make sure node is included first */
#include "expr/node.h"
#include "expr/type_node.h"

#ifndef CVC4__NODE_BUILDER_H
#define CVC4__NODE_BUILDER_H

#include <cstdlib>
#include <iostream>
#include <memory>
#include <stdint.h>
#include <vector>

namespace CVC4 {
  static const unsigned default_nchild_thresh = 10;

  template <unsigned nchild_thresh>
  class NodeBuilder;

  class NodeManager;
}/* CVC4 namespace */

#include "base/check.h"
#include "base/output.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_value.h"

namespace CVC4 {

// Sometimes it's useful for debugging to output a NodeBuilder that
// isn't yet a Node..
template <unsigned nchild_thresh>
std::ostream& operator<<(std::ostream& out, const NodeBuilder<nchild_thresh>& nb);

/**
 * The main template NodeBuilder.
 */
template <unsigned nchild_thresh = default_nchild_thresh>
class NodeBuilder {
  /**
   * An "in-line" stack-allocated buffer for use by the
   * NodeBuilder.
   */
  expr::NodeValue d_inlineNv;
  /**
   * Space for the children of the node being constructed.  This is
   * never accessed directly, but rather through
   * d_inlineNv.d_children[i].
   */
  expr::NodeValue* d_inlineNvChildSpace[nchild_thresh];

  /**
   * A pointer to the "current" NodeValue buffer; either &d_inlineNv
   * or a heap-allocated one if d_inlineNv wasn't big enough.
   */
  expr::NodeValue* d_nv;

  /** The NodeManager at play */
  NodeManager* d_nm;

  /**
   * The number of children allocated in d_nv.
   */
  uint32_t d_nvMaxChildren;

  template <unsigned N>
  void internalCopy(const NodeBuilder<N>& nb);

  /**
   * Returns whether or not this NodeBuilder has been "used"---i.e.,
   * whether a Node has been extracted with operator Node().
   * Internally, this state is represented by d_nv pointing to NULL.
   */
  inline bool isUsed() const {
    return __builtin_expect( ( d_nv == NULL ), false );
  }

  /**
   * Set this NodeBuilder to the `used' state.
   */
  inline void setUsed() {
    Assert(!isUsed()) << "Internal error: bad `used' state in NodeBuilder!";
    Assert(d_inlineNv.d_nchildren == 0 && d_nvMaxChildren == nchild_thresh)
        << "Internal error: bad `inline' state in NodeBuilder!";
    d_nv = NULL;
  }

  /**
   * Set this NodeBuilder to the `unused' state.  Should only be done
   * from clear().
   */
  inline void setUnused() {
    Assert(isUsed()) << "Internal error: bad `used' state in NodeBuilder!";
    Assert(d_inlineNv.d_nchildren == 0 && d_nvMaxChildren == nchild_thresh)
        << "Internal error: bad `inline' state in NodeBuilder!";
    d_nv = &d_inlineNv;
  }

  /**
   * Returns true if d_nv is *not* the "in-line" one (it was
   * heap-allocated by this class).
   */
  inline bool nvIsAllocated() const {
    return __builtin_expect( ( d_nv != &d_inlineNv ), false ) && __builtin_expect(( d_nv != NULL ), true );
  }

  /**
   * Returns true if adding a child requires (re)allocation of d_nv
   * first.
   */
  inline bool nvNeedsToBeAllocated() const {
    return __builtin_expect( ( d_nv->d_nchildren == d_nvMaxChildren ), false );
  }

  /**
   * (Re)allocate d_nv using a default grow factor.  Ensure that child
   * pointers are copied into the new buffer, and if the "inline"
   * NodeValue is evacuated, make sure its children won't be
   * double-decremented later (on destruction/clear).
   */
  inline void realloc()
  {
    size_t newSize = 2 * size_t(d_nvMaxChildren);
    size_t hardLimit = expr::NodeValue::MAX_CHILDREN;
    realloc(__builtin_expect((newSize > hardLimit), false) ? hardLimit
                                                           : newSize);
  }

  /**
   * (Re)allocate d_nv to a specific size.  Specify "copy" if the
   * children should be copied; if they are, and if the "inline"
   * NodeValue is evacuated, make sure its children won't be
   * double-decremented later (on destruction/clear).
   */
  void realloc(size_t toSize);

  /**
   * If d_nv needs to be (re)allocated to add an additional child, do
   * so using realloc(), which ensures child pointers are copied and
   * that the reference counts of the "inline" NodeValue won't be
   * double-decremented on destruction/clear.  Otherwise, do nothing.
   */
  inline void allocateNvIfNecessaryForAppend() {
    if(__builtin_expect( ( nvNeedsToBeAllocated() ), false )) {
      realloc();
    }
  }

  /**
   * Deallocate a d_nv that was heap-allocated by this class during
   * grow operations.  (Marks this NodeValue no longer allocated so
   * that double-deallocations don't occur.)
   *
   * PRECONDITION: only call this when nvIsAllocated() == true.
   * POSTCONDITION: !nvIsAllocated()
   */
  void dealloc();

  /**
   * "Purge" the "inline" children.  Decrement all their reference
   * counts and set the number of children to zero.
   *
   * PRECONDITION: only call this when nvIsAllocated() == false.
   * POSTCONDITION: d_inlineNv.d_nchildren == 0.
   */
  void decrRefCounts();

  /**
   * Trim d_nv down to the size it needs to be for the number of
   * children it has.  Used when a Node is extracted from a
   * NodeBuilder and we want the returned memory not to suffer from
   * internal fragmentation.  If d_nv was not heap-allocated by this
   * class, or is already the right size, this function does nothing.
   *
   * @throws bad_alloc if the reallocation fails
   */
  void crop() {
    if(__builtin_expect( ( nvIsAllocated() ), false ) &&
       __builtin_expect( ( d_nvMaxChildren > d_nv->d_nchildren ), true )) {
      // Ensure d_nv is not modified on allocation failure
      expr::NodeValue* newBlock = (expr::NodeValue*)
        std::realloc(d_nv,
                     sizeof(expr::NodeValue) +
                     ( sizeof(expr::NodeValue*) * d_nv->d_nchildren ));
      if(newBlock == NULL) {
        // In this case, d_nv was NOT freed.  If we throw, the
        // deallocation should occur on destruction of the
        // NodeBuilder.
        throw std::bad_alloc();
      }
      d_nv = newBlock;
      d_nvMaxChildren = d_nv->d_nchildren;
    }
  }

  // used by convenience node builders
  NodeBuilder<nchild_thresh>& collapseTo(Kind k) {
    AssertArgument(k != kind::UNDEFINED_KIND &&
                   k != kind::NULL_EXPR &&
                   k < kind::LAST_KIND,
                   k, "illegal collapsing kind");

    if(getKind() != k) {
      Node n = operator Node();
      clear();
      d_nv->d_kind = expr::NodeValue::kindToDKind(k);
      d_nv->d_id = 1; // have a kind already
      return append(n);
    }
    return *this;
  }

public:

  inline NodeBuilder() :
    d_nv(&d_inlineNv),
    d_nm(NodeManager::currentNM()),
    d_nvMaxChildren(nchild_thresh) {

    d_inlineNv.d_id = 0;
    d_inlineNv.d_rc = 0;
    d_inlineNv.d_kind = expr::NodeValue::kindToDKind(kind::UNDEFINED_KIND);
    d_inlineNv.d_nchildren = 0;
  }

  inline NodeBuilder(Kind k) :
    d_nv(&d_inlineNv),
    d_nm(NodeManager::currentNM()),
    d_nvMaxChildren(nchild_thresh) {
    Assert(k != kind::NULL_EXPR && k != kind::UNDEFINED_KIND)
        << "illegal Node-building kind";

    d_inlineNv.d_id = 1; // have a kind already
    d_inlineNv.d_rc = 0;
    d_inlineNv.d_kind = expr::NodeValue::kindToDKind(k);
    d_inlineNv.d_nchildren = 0;
  }

  inline NodeBuilder(NodeManager* nm) :
    d_nv(&d_inlineNv),
    d_nm(nm),
    d_nvMaxChildren(nchild_thresh) {

    d_inlineNv.d_id = 0;
    d_inlineNv.d_rc = 0;
    d_inlineNv.d_kind = expr::NodeValue::kindToDKind(kind::UNDEFINED_KIND);
    d_inlineNv.d_nchildren = 0;
  }

  inline NodeBuilder(NodeManager* nm, Kind k) :
    d_nv(&d_inlineNv),
    d_nm(nm),
    d_nvMaxChildren(nchild_thresh) {
    Assert(k != kind::NULL_EXPR && k != kind::UNDEFINED_KIND)
        << "illegal Node-building kind";

    d_inlineNv.d_id = 1; // have a kind already
    d_inlineNv.d_rc = 0;
    d_inlineNv.d_kind = expr::NodeValue::kindToDKind(k);
    d_inlineNv.d_nchildren = 0;
  }

  inline ~NodeBuilder() {
    if(__builtin_expect( ( nvIsAllocated() ), false )) {
      dealloc();
    } else if(__builtin_expect( ( !isUsed() ), false )) {
      decrRefCounts();
    }
  }

  // These implementations are identical, but we need to have both of
  // these because the templatized version isn't recognized as a
  // generalization of a copy constructor (and a default copy
  // constructor will be generated [?])
  inline NodeBuilder(const NodeBuilder& nb) :
    d_nv(&d_inlineNv),
    d_nm(nb.d_nm),
    d_nvMaxChildren(nchild_thresh) {

    d_inlineNv.d_id = nb.d_nv->d_id;
    d_inlineNv.d_rc = 0;
    d_inlineNv.d_kind = nb.d_nv->d_kind;
    d_inlineNv.d_nchildren = 0;

    internalCopy(nb);
  }

  // technically this is a conversion, not a copy
  template <unsigned N>
  inline NodeBuilder(const NodeBuilder<N>& nb) :
    d_nv(&d_inlineNv),
    d_nm(nb.d_nm),
    d_nvMaxChildren(nchild_thresh) {

    d_inlineNv.d_id = nb.d_nv->d_id;
    d_inlineNv.d_rc = 0;
    d_inlineNv.d_kind = nb.d_nv->d_kind;
    d_inlineNv.d_nchildren = 0;

    internalCopy(nb);
  }

  typedef expr::NodeValue::iterator< NodeTemplate<true>  > iterator;
  typedef expr::NodeValue::iterator< NodeTemplate<true> > const_iterator;

  /** Get the begin-const-iterator of this Node-under-construction. */
  inline const_iterator begin() const {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    Assert(getKind() != kind::UNDEFINED_KIND)
        << "Iterators over NodeBuilder<> are undefined "
           "until a Kind is set";
    return d_nv->begin< NodeTemplate<true> >();
  }

  /** Get the end-const-iterator of this Node-under-construction. */
  inline const_iterator end() const {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    Assert(getKind() != kind::UNDEFINED_KIND)
        << "Iterators over NodeBuilder<> are undefined "
           "until a Kind is set";
    return d_nv->end< NodeTemplate<true> >();
  }

  /** Get the kind of this Node-under-construction. */
  inline Kind getKind() const {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    return d_nv->getKind();
  }

  /** Get the kind of this Node-under-construction. */
  inline kind::MetaKind getMetaKind() const {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    Assert(getKind() != kind::UNDEFINED_KIND)
        << "The metakind of a NodeBuilder<> is undefined "
           "until a Kind is set";
    return d_nv->getMetaKind();
  }

  /** Get the current number of children of this Node-under-construction. */
  inline unsigned getNumChildren() const {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    Assert(getKind() != kind::UNDEFINED_KIND)
        << "The number of children of a NodeBuilder<> is undefined "
           "until a Kind is set";
    return d_nv->getNumChildren();
  }

  /**
   * Access to the operator of this Node-under-construction.  Only
   * allowed if this NodeBuilder is unused, and has a defined kind
   * that is of PARAMETERIZED metakind.
   */
  inline Node getOperator() const {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    Assert(getKind() != kind::UNDEFINED_KIND)
        << "NodeBuilder<> operator access is not permitted "
           "until a Kind is set";
    Assert(getMetaKind() == kind::metakind::PARAMETERIZED)
        << "NodeBuilder<> operator access is only permitted "
           "on parameterized kinds, not `"
        << getKind() << "'";
    return Node(d_nv->getOperator());
  }

  /**
   * Access to children of this Node-under-construction.  Only allowed
   * if this NodeBuilder is unused and has a defined kind.
   */
  inline Node getChild(int i) const {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    Assert(getKind() != kind::UNDEFINED_KIND)
        << "NodeBuilder<> child access is not permitted "
           "until a Kind is set";
    Assert(i >= 0 && unsigned(i) < d_nv->getNumChildren())
        << "index out of range for NodeBuilder::getChild()";
    return Node(d_nv->getChild(i));
  }

  /** Access to children of this Node-under-construction. */
  inline Node operator[](int i) const {
    return getChild(i);
  }

  /**
   * "Reset" this node builder (optionally setting a new kind for it),
   * using the same "inline" memory as at construction time.  This
   * deallocates NodeBuilder-allocated heap memory, if it was
   * allocated, and decrements the reference counts of any currently
   * children in the NodeBuilder.
   *
   * This should leave the NodeBuilder in the state it was after
   * initial construction, except for Kind, which is set to the
   * argument, if provided, or UNDEFINED_KIND.  In particular, the
   * associated NodeManager is not affected by clear().
   */
  void clear(Kind k = kind::UNDEFINED_KIND);

  // "Stream" expression constructor syntax

  /** Set the Kind of this Node-under-construction. */
  inline NodeBuilder<nchild_thresh>& operator<<(const Kind& k) {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    Assert(getKind() == kind::UNDEFINED_KIND || d_nv->d_id == 0)
        << "can't redefine the Kind of a NodeBuilder";
    Assert(d_nv->d_id == 0)
        << "internal inconsistency with NodeBuilder: d_id != 0";
    AssertArgument(k != kind::UNDEFINED_KIND &&
                   k != kind::NULL_EXPR &&
                   k < kind::LAST_KIND,
                   k, "illegal node-building kind");
    // This test means: we didn't have a Kind at the beginning (on
    // NodeBuilder construction or at the last clear()), but we do
    // now.  That means we appended a Kind with operator<<(Kind),
    // which now (lazily) we'll collapse.
    if(__builtin_expect( ( d_nv->d_id == 0 && getKind() != kind::UNDEFINED_KIND ), false )) {
      Node n2 = operator Node();
      clear();
      append(n2);
    } else if(d_nv->d_nchildren == 0) {
      d_nv->d_id = 1; // remember that we had a kind from the start
    }
    d_nv->d_kind = expr::NodeValue::kindToDKind(k);
    return *this;
  }

  /**
   * If this Node-under-construction has a Kind set, collapse it and
   * append the given Node as a child.  Otherwise, simply append.
   */
  NodeBuilder<nchild_thresh>& operator<<(TNode n) {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    // This test means: we didn't have a Kind at the beginning (on
    // NodeBuilder construction or at the last clear()), but we do
    // now.  That means we appended a Kind with operator<<(Kind),
    // which now (lazily) we'll collapse.
    if(__builtin_expect( ( d_nv->d_id == 0 && getKind() != kind::UNDEFINED_KIND ), false )) {
      Node n2 = operator Node();
      clear();
      append(n2);
    }
    return append(n);
  }

  /**
   * If this Node-under-construction has a Kind set, collapse it and
   * append the given Node as a child.  Otherwise, simply append.
   */
  NodeBuilder<nchild_thresh>& operator<<(TypeNode n) {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    // This test means: we didn't have a Kind at the beginning (on
    // NodeBuilder construction or at the last clear()), but we do
    // now.  That means we appended a Kind with operator<<(Kind),
    // which now (lazily) we'll collapse.
    if(__builtin_expect( ( d_nv->d_id == 0 && getKind() != kind::UNDEFINED_KIND ), false )) {
      Node n2 = operator Node();
      clear();
      append(n2);
    }
    return append(n);
  }

  /** Append a sequence of children to this TypeNode-under-construction. */
  inline NodeBuilder<nchild_thresh>&
  append(const std::vector<TypeNode>& children) {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    return append(children.begin(), children.end());
  }

  /** Append a sequence of children to this Node-under-construction. */
  template <bool ref_count>
  inline NodeBuilder<nchild_thresh>&
  append(const std::vector<NodeTemplate<ref_count> >& children) {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    return append(children.begin(), children.end());
  }

  /** Append a sequence of children to this Node-under-construction. */
  template <class Iterator>
  NodeBuilder<nchild_thresh>& append(const Iterator& begin, const Iterator& end) {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    for(Iterator i = begin; i != end; ++i) {
      append(*i);
    }
    return *this;
  }

  /** Append a child to this Node-under-construction. */
  NodeBuilder<nchild_thresh>& append(TNode n) {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    Assert(!n.isNull()) << "Cannot use NULL Node as a child of a Node";
    if(n.getKind() == kind::BUILTIN) {
      return *this << NodeManager::operatorToKind(n);
    }
    allocateNvIfNecessaryForAppend();
    expr::NodeValue* nv = n.d_nv;
    nv->inc();
    d_nv->d_children[d_nv->d_nchildren++] = nv;
    Assert(d_nv->d_nchildren <= d_nvMaxChildren);
    return *this;
  }

  /** Append a child to this Node-under-construction. */
  NodeBuilder<nchild_thresh>& append(const TypeNode& typeNode) {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    Assert(!typeNode.isNull()) << "Cannot use NULL Node as a child of a Node";
    allocateNvIfNecessaryForAppend();
    expr::NodeValue* nv = typeNode.d_nv;
    nv->inc();
    d_nv->d_children[d_nv->d_nchildren++] = nv;
    Assert(d_nv->d_nchildren <= d_nvMaxChildren);
    return *this;
  }

private:

  /** Construct the node value out of the node builder */
  expr::NodeValue* constructNV();
  expr::NodeValue* constructNV() const;

#ifdef CVC4_DEBUG
  // Throws a TypeCheckingExceptionPrivate on a failure.
  void maybeCheckType(const TNode n) const;
#else /* CVC4_DEBUG */
  // Do nothing if not in debug mode.
  inline void maybeCheckType(const TNode n) const {}
#endif /* CVC4_DEBUG */

public:

  /** Construct the Node out of the node builder */
  Node constructNode();
  Node constructNode() const;

  /** Construct a Node on the heap out of the node builder */
  Node* constructNodePtr();
  Node* constructNodePtr() const;

  /** Construction of the TypeNode out of the node builder */
  TypeNode constructTypeNode();
  TypeNode constructTypeNode() const;

  // two versions, so we can support extraction from (const)
  // NodeBuilders which are temporaries appearing as rvalues
  operator Node();
  operator Node() const;

  // similarly for TypeNode
  operator TypeNode();
  operator TypeNode() const;

  NodeBuilder<nchild_thresh>& operator&=(TNode);
  NodeBuilder<nchild_thresh>& operator|=(TNode);
  NodeBuilder<nchild_thresh>& operator+=(TNode);
  NodeBuilder<nchild_thresh>& operator-=(TNode);
  NodeBuilder<nchild_thresh>& operator*=(TNode);

  // This is needed for copy constructors of different sizes to access
  // private fields
  template <unsigned N>
  friend class NodeBuilder;

  template <unsigned N>
  friend std::ostream& operator<<(std::ostream& out, const NodeBuilder<N>& nb);

};/* class NodeBuilder<> */

}/* CVC4 namespace */

// TODO: add templatized NodeTemplate<ref_count> to all above and
// below inlines for 'const [T]Node&' arguments?  Technically a lot of
// time is spent in the TNode conversion and copy constructor, but
// this should be optimized into a simple pointer copy (?)
// TODO: double-check this.

#include "expr/node.h"
#include "expr/node_manager.h"
#include "options/expr_options.h"

namespace CVC4 {

template <unsigned nchild_thresh>
void NodeBuilder<nchild_thresh>::clear(Kind k) {
  Assert(k != kind::NULL_EXPR) << "illegal Node-building clear kind";

  if(__builtin_expect( ( nvIsAllocated() ), false )) {
    dealloc();
  } else if(__builtin_expect( ( !isUsed() ), false )) {
    decrRefCounts();
  } else {
    setUnused();
  }

  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(k);
  for(expr::NodeValue::nv_iterator i = d_inlineNv.nv_begin();
      i != d_inlineNv.nv_end();
      ++i) {
    (*i)->dec();
  }
  d_inlineNv.d_nchildren = 0;
  // keep track of whether or not we hvae a kind already
  d_inlineNv.d_id = (k == kind::UNDEFINED_KIND) ? 0 : 1;
}

template <unsigned nchild_thresh>
void NodeBuilder<nchild_thresh>::realloc(size_t toSize) {
  AlwaysAssert(toSize > d_nvMaxChildren)
      << "attempt to realloc() a NodeBuilder to a smaller/equal size!";
  Assert(toSize < (static_cast<size_t>(1) << expr::NodeValue::NBITS_NCHILDREN))
      << "attempt to realloc() a NodeBuilder to size " << toSize
      << " (beyond hard limit of " << expr::NodeValue::MAX_CHILDREN << ")";

  if(__builtin_expect( ( nvIsAllocated() ), false )) {
    // Ensure d_nv is not modified on allocation failure
    expr::NodeValue* newBlock = (expr::NodeValue*)
      std::realloc(d_nv, sizeof(expr::NodeValue) +
                   ( sizeof(expr::NodeValue*) * toSize ));
    if(newBlock == NULL) {
      // In this case, d_nv was NOT freed.  If we throw, the
      // deallocation should occur on destruction of the NodeBuilder.
      throw std::bad_alloc();
    }
    d_nvMaxChildren = toSize;
    Assert(d_nvMaxChildren == toSize);  // overflow check
    // Here, the copy (between two heap-allocated buffers) has already
    // been done for us by the std::realloc().
    d_nv = newBlock;
  } else {
    // Ensure d_nv is not modified on allocation failure
    expr::NodeValue* newBlock = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue) +
                  ( sizeof(expr::NodeValue*) * toSize ));
    if(newBlock == NULL) {
      throw std::bad_alloc();
    }
    d_nvMaxChildren = toSize;
    Assert(d_nvMaxChildren == toSize);  // overflow check

    d_nv = newBlock;
    d_nv->d_id = d_inlineNv.d_id;
    d_nv->d_rc = 0;
    d_nv->d_kind = d_inlineNv.d_kind;
    d_nv->d_nchildren = d_inlineNv.d_nchildren;

    std::copy(d_inlineNv.d_children,
              d_inlineNv.d_children + d_inlineNv.d_nchildren,
              d_nv->d_children);

    // ensure "inline" children don't get decremented in dtor
    d_inlineNv.d_nchildren = 0;
  }
}

template <unsigned nchild_thresh>
void NodeBuilder<nchild_thresh>::dealloc() {
  Assert(nvIsAllocated())
      << "Internal error: NodeBuilder: dealloc() called without a "
         "private NodeBuilder-allocated buffer";

  for(expr::NodeValue::nv_iterator i = d_nv->nv_begin();
      i != d_nv->nv_end();
      ++i) {
    (*i)->dec();
  }

  free(d_nv);
  d_nv = &d_inlineNv;
  d_nvMaxChildren = nchild_thresh;
}

template <unsigned nchild_thresh>
void NodeBuilder<nchild_thresh>::decrRefCounts() {
  Assert(!nvIsAllocated())
      << "Internal error: NodeBuilder: decrRefCounts() called with a "
         "private NodeBuilder-allocated buffer";

  for(expr::NodeValue::nv_iterator i = d_inlineNv.nv_begin();
      i != d_inlineNv.nv_end();
      ++i) {
    (*i)->dec();
  }

  d_inlineNv.d_nchildren = 0;
}


template <unsigned nchild_thresh>
TypeNode NodeBuilder<nchild_thresh>::constructTypeNode() {
  return TypeNode(constructNV());
}

template <unsigned nchild_thresh>
TypeNode NodeBuilder<nchild_thresh>::constructTypeNode() const {
  return TypeNode(constructNV());
}

template <unsigned nchild_thresh>
Node NodeBuilder<nchild_thresh>::constructNode() {
  Node n = Node(constructNV());
  maybeCheckType(n);
  return n;
}

template <unsigned nchild_thresh>
Node NodeBuilder<nchild_thresh>::constructNode() const {
  Node n = Node(constructNV());
  maybeCheckType(n);
  return n;
}

template <unsigned nchild_thresh>
Node* NodeBuilder<nchild_thresh>::constructNodePtr() {
  // maybeCheckType() can throw an exception. Make sure to call the destructor
  // on the exception branch.
  std::unique_ptr<Node> np(new Node(constructNV()));
  maybeCheckType(*np.get());
  return np.release();
}

template <unsigned nchild_thresh>
Node* NodeBuilder<nchild_thresh>::constructNodePtr() const {
  std::unique_ptr<Node> np(new Node(constructNV()));
  maybeCheckType(*np.get());
  return np.release();
}

template <unsigned nchild_thresh>
NodeBuilder<nchild_thresh>::operator Node() {
  return constructNode();
}

template <unsigned nchild_thresh>
NodeBuilder<nchild_thresh>::operator Node() const {
  return constructNode();
}

template <unsigned nchild_thresh>
NodeBuilder<nchild_thresh>::operator TypeNode() {
  return constructTypeNode();
}

template <unsigned nchild_thresh>
NodeBuilder<nchild_thresh>::operator TypeNode() const {
  return constructTypeNode();
}

template <unsigned nchild_thresh>
expr::NodeValue* NodeBuilder<nchild_thresh>::constructNV() {
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  Assert(getKind() != kind::UNDEFINED_KIND)
      << "Can't make an expression of an undefined kind!";

  // NOTE: The comments in this function refer to the cases in the
  // file comments at the top of this file.

  // Case 0: If a VARIABLE
  if(getMetaKind() == kind::metakind::VARIABLE || getMetaKind() == kind::metakind::NULLARY_OPERATOR) {
    /* 0. If a VARIABLE, treat similarly to 1(b), except that we know
     * there are no children (no reference counts to reason about),
     * and we don't keep VARIABLE-kinded Nodes in the NodeManager
     * pool. */

    Assert(!nvIsAllocated())
        << "internal NodeBuilder error: "
           "VARIABLE-kinded NodeBuilder is heap-allocated !?";
    Assert(d_inlineNv.d_nchildren == 0)
        << "improperly-formed VARIABLE-kinded NodeBuilder: "
           "no children permitted";

    // we have to copy the inline NodeValue out
    expr::NodeValue* nv = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue));
    if(nv == NULL) {
      throw std::bad_alloc();
    }
    // there are no children, so we don't have to worry about
    // reference counts in this case.
    nv->d_nchildren = 0;
    nv->d_kind = d_nv->d_kind;
    nv->d_id = d_nm->next_id++;// FIXME multithreading
    nv->d_rc = 0;
    setUsed();
    if(Debug.isOn("gc")) {
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: ";
      nv->printAst(Debug("gc"));
      Debug("gc") << std::endl;
    }
    return nv;
  }

  // check that there are the right # of children for this kind
  Assert(getMetaKind() != kind::metakind::CONSTANT)
      << "Cannot make Nodes with NodeBuilder that have CONSTANT-kinded kinds";
  Assert(getNumChildren() >= kind::metakind::getLowerBoundForKind(getKind()))
      << "Nodes with kind " << getKind() << " must have at least "
      << kind::metakind::getLowerBoundForKind(getKind())
      << " children (the one under "
         "construction has "
      << getNumChildren() << ")";
  Assert(getNumChildren() <= kind::metakind::getUpperBoundForKind(getKind()))
      << "Nodes with kind " << getKind() << " must have at most "
      << kind::metakind::getUpperBoundForKind(getKind())
      << " children (the one under "
         "construction has "
      << getNumChildren() << ")";

  // Implementation differs depending on whether the NodeValue was
  // malloc'ed or not and whether or not it's in the already-been-seen
  // NodeManager pool of Nodes.  See implementation notes at the top
  // of this file.

  if(__builtin_expect( ( ! nvIsAllocated() ), true )) {
    /** Case 1.  d_nv points to d_inlineNv: it is the backing store
     ** allocated "inline" in this NodeBuilder. **/

    // Lookup the expression value in the pool we already have
    expr::NodeValue* poolNv = d_nm->poolLookup(&d_inlineNv);
    // If something else is there, we reuse it
    if(poolNv != NULL) {
      /* Subcase (a): The Node under construction already exists in
       * the NodeManager's pool. */

      /* 1(a). Reference-counts for all children in d_inlineNv must be
       * decremented, and the NodeBuilder must be marked as "used" and
       * the number of children set to zero so that we don't decrement
       * them again on destruction.  The existing NodeManager pool
       * entry is returned.
       */
      decrRefCounts();
      d_inlineNv.d_nchildren = 0;
      setUsed();
      return poolNv;
    } else {
      /* Subcase (b): The Node under construction is NOT already in
       * the NodeManager's pool. */

      /* 1(b). A new heap-allocated NodeValue must be constructed and
       * all settings and children from d_inlineNv copied into it.
       * This new NodeValue is put into the NodeManager's pool.  The
       * NodeBuilder is marked as "used" and the number of children in
       * d_inlineNv set to zero so that we don't decrement child
       * reference counts on destruction (the child reference counts
       * have been "taken over" by the new NodeValue).  We return a
       * Node wrapper for this new NodeValue, which increments its
       * reference count. */

      // create the canonical expression value for this node
      expr::NodeValue* nv = (expr::NodeValue*)
        std::malloc(sizeof(expr::NodeValue) +
                    ( sizeof(expr::NodeValue*) * d_inlineNv.d_nchildren ));
      if(nv == NULL) {
        throw std::bad_alloc();
      }
      nv->d_nchildren = d_inlineNv.d_nchildren;
      nv->d_kind = d_inlineNv.d_kind;
      nv->d_id = d_nm->next_id++;// FIXME multithreading
      nv->d_rc = 0;

      std::copy(d_inlineNv.d_children,
                d_inlineNv.d_children + d_inlineNv.d_nchildren,
                nv->d_children);

      d_inlineNv.d_nchildren = 0;
      setUsed();

      //poolNv = nv;
      d_nm->poolInsert(nv);
      if(Debug.isOn("gc")) {
        Debug("gc") << "creating node value " << nv
                    << " [" << nv->d_id << "]: ";
        nv->printAst(Debug("gc"));
        Debug("gc") << std::endl;
      }
      return nv;
    }
  } else {
    /** Case 2. d_nv does NOT point to d_inlineNv: it is a new, larger
     ** buffer that was heap-allocated by this NodeBuilder. **/

    // Lookup the expression value in the pool we already have (with insert)
    expr::NodeValue* poolNv = d_nm->poolLookup(d_nv);
    // If something else is there, we reuse it
    if(poolNv != NULL) {
      /* Subcase (a): The Node under construction already exists in
       * the NodeManager's pool. */

      /* 2(a). Reference-counts for all children in d_nv must be
       * decremented.  The NodeBuilder is marked as "used" and the
       * heap-allocated d_nv deleted.  d_nv is repointed to d_inlineNv
       * so that destruction of the NodeBuilder doesn't cause any
       * problems.  The existing NodeManager pool entry is
       * returned. */

      dealloc();
      setUsed();
      return poolNv;
    } else {
      /* Subcase (b) The Node under construction is NOT already in the
       * NodeManager's pool. */

      /* 2(b). The heap-allocated d_nv is "cropped" to the correct
       * size (based on the number of children it _actually_ has).
       * d_nv is repointed to d_inlineNv so that destruction of the
       * NodeBuilder doesn't cause any problems, and the (old) value
       * it had is placed into the NodeManager's pool and returned in
       * a Node wrapper. */

      crop();
      expr::NodeValue* nv = d_nv;
      nv->d_id = d_nm->next_id++;// FIXME multithreading
      d_nv = &d_inlineNv;
      d_nvMaxChildren = nchild_thresh;
      setUsed();

      //poolNv = nv;
      d_nm->poolInsert(nv);
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << *nv << "\n";
      return nv;
    }
  }
}

// CONST VERSION OF NODE EXTRACTOR
template <unsigned nchild_thresh>
expr::NodeValue* NodeBuilder<nchild_thresh>::constructNV() const {
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  Assert(getKind() != kind::UNDEFINED_KIND)
      << "Can't make an expression of an undefined kind!";

  // NOTE: The comments in this function refer to the cases in the
  // file comments at the top of this file.

  // Case 0: If a VARIABLE
  if(getMetaKind() == kind::metakind::VARIABLE || getMetaKind() == kind::metakind::NULLARY_OPERATOR) {
    /* 0. If a VARIABLE, treat similarly to 1(b), except that we know
     * there are no children (no reference counts to reason about),
     * and we don't keep VARIABLE-kinded Nodes in the NodeManager
     * pool. */

    Assert(!nvIsAllocated())
        << "internal NodeBuilder error: "
           "VARIABLE-kinded NodeBuilder is heap-allocated !?";
    Assert(d_inlineNv.d_nchildren == 0)
        << "improperly-formed VARIABLE-kinded NodeBuilder: "
           "no children permitted";

    // we have to copy the inline NodeValue out
    expr::NodeValue* nv = (expr::NodeValue*)
      std::malloc(sizeof(expr::NodeValue));
    if(nv == NULL) {
      throw std::bad_alloc();
    }
    // there are no children, so we don't have to worry about
    // reference counts in this case.
    nv->d_nchildren = 0;
    nv->d_kind = d_nv->d_kind;
    nv->d_id = d_nm->next_id++;// FIXME multithreading
    nv->d_rc = 0;
    Debug("gc") << "creating node value " << nv
                << " [" << nv->d_id << "]: " << *nv << "\n";
    return nv;
  }

  // check that there are the right # of children for this kind
  Assert(getMetaKind() != kind::metakind::CONSTANT)
      << "Cannot make Nodes with NodeBuilder that have CONSTANT-kinded kinds";
  Assert(getNumChildren() >= kind::metakind::getLowerBoundForKind(getKind()))
      << "Nodes with kind " << getKind() << " must have at least "
      << kind::metakind::getLowerBoundForKind(getKind())
      << " children (the one under "
         "construction has "
      << getNumChildren() << ")";
  Assert(getNumChildren() <= kind::metakind::getUpperBoundForKind(getKind()))
      << "Nodes with kind " << getKind() << " must have at most "
      << kind::metakind::getUpperBoundForKind(getKind())
      << " children (the one under "
         "construction has "
      << getNumChildren() << ")";

#if 0
  // if the kind is PARAMETERIZED, check that the operator is correctly-kinded
  Assert(kind::metaKindOf(getKind()) != kind::metakind::PARAMETERIZED ||
         NodeManager::operatorToKind(getOperator()) == getKind()) << 
         "Attempted to construct a parameterized kind `"<< getKind() <<"' with "
         "incorrectly-kinded operator `"<< getOperator().getKind() <<"'";
#endif /* 0 */

  // Implementation differs depending on whether the NodeValue was
  // malloc'ed or not and whether or not it's in the already-been-seen
  // NodeManager pool of Nodes.  See implementation notes at the top
  // of this file.

  if(__builtin_expect( ( ! nvIsAllocated() ), true )) {
    /** Case 1.  d_nv points to d_inlineNv: it is the backing store
     ** allocated "inline" in this NodeBuilder. **/

    // Lookup the expression value in the pool we already have
    expr::NodeValue* poolNv = d_nm->poolLookup(const_cast<expr::NodeValue*>(&d_inlineNv));
    // If something else is there, we reuse it
    if(poolNv != NULL) {
      /* Subcase (a): The Node under construction already exists in
       * the NodeManager's pool. */

      /* 1(a). The existing NodeManager pool entry is returned; we
       * leave child reference counts alone and get them at
       * NodeBuilder destruction time. */

      return poolNv;
    } else {
      /* Subcase (b): The Node under construction is NOT already in
       * the NodeManager's pool. */

      /* 1(b). A new heap-allocated NodeValue must be constructed and
       * all settings and children from d_inlineNv copied into it.
       * This new NodeValue is put into the NodeManager's pool.  The
       * NodeBuilder cannot be marked as "used", so we increment all
       * child reference counts (which will be decremented to match on
       * destruction of the NodeBuilder).  We return a Node wrapper
       * for this new NodeValue, which increments its reference
       * count. */

      // create the canonical expression value for this node
      expr::NodeValue* nv = (expr::NodeValue*)
        std::malloc(sizeof(expr::NodeValue) +
                    ( sizeof(expr::NodeValue*) * d_inlineNv.d_nchildren ));
      if(nv == NULL) {
        throw std::bad_alloc();
      }
      nv->d_nchildren = d_inlineNv.d_nchildren;
      nv->d_kind = d_inlineNv.d_kind;
      nv->d_id = d_nm->next_id++;// FIXME multithreading
      nv->d_rc = 0;

      std::copy(d_inlineNv.d_children,
                d_inlineNv.d_children + d_inlineNv.d_nchildren,
                nv->d_children);

      for(expr::NodeValue::nv_iterator i = nv->nv_begin();
          i != nv->nv_end();
          ++i) {
        (*i)->inc();
      }

      //poolNv = nv;
      d_nm->poolInsert(nv);
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << *nv << "\n";
      return nv;
    }
  } else {
    /** Case 2. d_nv does NOT point to d_inlineNv: it is a new, larger
     ** buffer that was heap-allocated by this NodeBuilder. **/

    // Lookup the expression value in the pool we already have (with insert)
    expr::NodeValue* poolNv = d_nm->poolLookup(d_nv);
    // If something else is there, we reuse it
    if(poolNv != NULL) {
      /* Subcase (a): The Node under construction already exists in
       * the NodeManager's pool. */

      /* 2(a). The existing NodeManager pool entry is returned; we
       * leave child reference counts alone and get them at
       * NodeBuilder destruction time. */

      return poolNv;
    } else {
      /* Subcase (b) The Node under construction is NOT already in the
       * NodeManager's pool. */

      /* 2(b). The heap-allocated d_nv cannot be "cropped" to the
       * correct size; we create a copy, increment child reference
       * counts, place this copy into the NodeManager pool, and return
       * a Node wrapper around it.  The child reference counts will be
       * decremented to match at NodeBuilder destruction time. */

      // create the canonical expression value for this node
      expr::NodeValue* nv = (expr::NodeValue*)
        std::malloc(sizeof(expr::NodeValue) +
                    ( sizeof(expr::NodeValue*) * d_nv->d_nchildren ));
      if(nv == NULL) {
        throw std::bad_alloc();
      }
      nv->d_nchildren = d_nv->d_nchildren;
      nv->d_kind = d_nv->d_kind;
      nv->d_id = d_nm->next_id++;// FIXME multithreading
      nv->d_rc = 0;

      std::copy(d_nv->d_children,
                d_nv->d_children + d_nv->d_nchildren,
                nv->d_children);

      for(expr::NodeValue::nv_iterator i = nv->nv_begin();
          i != nv->nv_end();
          ++i) {
        (*i)->inc();
      }

      //poolNv = nv;
      d_nm->poolInsert(nv);
      Debug("gc") << "creating node value " << nv
                  << " [" << nv->d_id << "]: " << *nv << "\n";
      return nv;
    }
  }
}

template <unsigned nchild_thresh>
template <unsigned N>
void NodeBuilder<nchild_thresh>::internalCopy(const NodeBuilder<N>& nb) {
  if(nb.isUsed()) {
    setUsed();
    return;
  }

  bool realloced CVC4_UNUSED = false;
  if(nb.d_nvMaxChildren > d_nvMaxChildren) {
    realloced = true;
    realloc(nb.d_nvMaxChildren);
  }

  Assert(nb.d_nvMaxChildren <= d_nvMaxChildren);
  Assert(nb.d_nv->nv_end() >= nb.d_nv->nv_begin());
  Assert((size_t)(nb.d_nv->nv_end() - nb.d_nv->nv_begin()) <= d_nvMaxChildren)
      << "realloced:" << (realloced ? "true" : "false")
      << ", d_nvMax:" << d_nvMaxChildren
      << ", size:" << nb.d_nv->nv_end() - nb.d_nv->nv_begin()
      << ", nc:" << nb.d_nv->getNumChildren();
  std::copy(nb.d_nv->nv_begin(), nb.d_nv->nv_end(), d_nv->nv_begin());

  d_nv->d_nchildren = nb.d_nv->d_nchildren;

  for(expr::NodeValue::nv_iterator i = d_nv->nv_begin();
      i != d_nv->nv_end();
      ++i) {
    (*i)->inc();
  }
}

#ifdef CVC4_DEBUG
template <unsigned nchild_thresh>
inline void NodeBuilder<nchild_thresh>::maybeCheckType(const TNode n) const
{
  /* force an immediate type check, if early type checking is
     enabled and the current node isn't a variable or constant */
  kind::MetaKind mk = n.getMetaKind();
  if (mk != kind::metakind::VARIABLE && mk != kind::metakind::NULLARY_OPERATOR
      && mk != kind::metakind::CONSTANT)
  {
    d_nm->getType(n, true);
  }
}
#endif /* CVC4_DEBUG */

template <unsigned nchild_thresh>
std::ostream& operator<<(std::ostream& out, const NodeBuilder<nchild_thresh>& nb) {
  return out << *nb.d_nv;
}

}/* CVC4 namespace */

#endif /* CVC4__NODE_BUILDER_H */
