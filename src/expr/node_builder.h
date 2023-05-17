/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andres Noetzli, Dejan Jovanovic
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A builder interface for Nodes.
 *
 * The idea is to permit a flexible and efficient (in the common
 * case) interface for building Nodes.  The general pattern of use is
 * to create a NodeBuilder, set its kind, append children to it, then
 * "extract" the resulting Node.  This resulting Node may be one that
 * already exists (the NodeManager keeps a table of all Nodes in the
 * system), or may be entirely new.
 *
 * This implementation gets a bit hairy for a handful of reasons.  We
 * want a user-supplied "in-line" buffer (probably on the stack, see
 * below) to hold the children, but then the number of children must
 * be known ahead of time.  Therefore, if this buffer is overrun, we
 * need to heap-allocate a new buffer to hold the children.
 *
 * Note that as children are added to a NodeBuilder, they are stored
 * as raw pointers-to-NodeValue.  However, their reference counts are
 * carefully maintained.
 *
 * When the "in-line" buffer "d_inlineNv" is superceded by a
 * heap-allocated buffer, we allocate the new buffer (a NodeValue
 * large enough to hold more children), copy the elements to it, and
 * mark d_inlineNv as having zero children.  We do this last bit so
 * that we don't have to modify any child reference counts.  The new
 * heap-allocated buffer "takes over" the reference counts of the old
 * "in-line" buffer.  (If we didn't mark it as having zero children,
 * the destructor may improperly decrement the children's reference
 * counts.)
 *
 * There are then four normal cases at the end of a NodeBuilder's
 * life cycle:
 *
 *   0. We have a VARIABLE-kinded Node.  These are special (they have
 *      no children and are all distinct by definition).  They are
 *      really a subcase of 1(b), below.
 *   1. d_nv points to d_inlineNv: it is the backing store supplied
 *      by the user (or derived class).
 *      (a) The Node under construction already exists in the
 *          NodeManager's pool.
 *      (b) The Node under construction is NOT already in the
 *          NodeManager's pool.
 *   2. d_nv does NOT point to d_inlineNv: it is a new, larger buffer
 *      that was heap-allocated by this NodeBuilder.
 *      (a) The Node under construction already exists in the
 *          NodeManager's pool.
 *      (b) The Node under construction is NOT already in the
 *          NodeManager's pool.
 *
 * When a Node is extracted, we convert the NodeBuilder to a Node and
 * make sure the reference counts are properly maintained.  That
 * means we must ensure there are no reference-counting errors among
 * the node's children, that the children aren't re-decremented on
 * clear() or NodeBuilder destruction, and that the returned Node
 * wraps a NodeValue with a reference count of 1.
 *
 *   0.    If a VARIABLE, treat similarly to 1(b), except that we
 *         know there are no children (no reference counts to reason
 *         about) and we don't keep VARIABLE-kinded Nodes in the
 *         NodeManager pool.
 *
 *   1(a). Reference-counts for all children in d_inlineNv must be
 *         decremented, and the NodeBuilder must be marked as "used"
 *         and the number of children set to zero so that we don't
 *         decrement them again on destruction.  The existing
 *         NodeManager pool entry is returned.
 *
 *   1(b). A new heap-allocated NodeValue must be constructed and all
 *         settings and children from d_inlineNv copied into it.
 *         This new NodeValue is put into the NodeManager's pool.
 *         The NodeBuilder is marked as "used" and the number of
 *         children in d_inlineNv set to zero so that we don't
 *         decrement child reference counts on destruction (the child
 *         reference counts have been "taken over" by the new
 *         NodeValue).  We return a Node wrapper for this new
 *         NodeValue, which increments its reference count.
 *
 *   2(a). Reference counts for all children in d_nv must be
 *         decremented.  The NodeBuilder is marked as "used" and the
 *         heap-allocated d_nv deleted.  d_nv is repointed to
 *         d_inlineNv so that destruction of the NodeBuilder doesn't
 *         cause any problems.  The existing NodeManager pool entry
 *         is returned.
 *
 *   2(b). The heap-allocated d_nv is "cropped" to the correct size
 *         (based on the number of children it _actually_ has).  d_nv
 *         is repointed to d_inlineNv so that destruction of the
 *         NodeBuilder doesn't cause any problems, and the (old)
 *         value it had is placed into the NodeManager's pool and
 *         returned in a Node wrapper.
 *
 * NOTE IN 1(b) AND 2(b) THAT we can NOT create Node wrapper
 * temporary for the NodeValue in the NodeBuilder::operator Node()
 * member function.  If we create a temporary (for example by writing
 * Trace("builder") << Node(nv) << endl), the NodeValue will have its
 * reference count incremented from zero to one, then decremented,
 * which makes it eligible for collection before the builder has even
 * returned it!  So this is a no-no.
 *
 * There are also two cases when the NodeBuilder is clear()'ed:
 *
 *   1. d_nv == &d_inlineNv (NodeBuilder using the user-supplied
 *      backing store): all d_inlineNv children have their reference
 *      counts decremented, d_inlineNv.d_nchildren is set to zero,
 *      and its kind is set to UNDEFINED_KIND.
 *
 *   2. d_nv != &d_inlineNv (d_nv heap-allocated by NodeBuilder): all
 *      d_nv children have their reference counts decremented, d_nv
 *      is deallocated, and d_nv is set to &d_inlineNv.  d_inlineNv's
 *      kind is set to UNDEFINED_KIND.
 *
 * ... destruction is similar:
 *
 *   1. d_nv == &d_inlineNv (NodeBuilder using the user-supplied
 *      backing store): all d_inlineNv children have their reference
 *      counts decremented.
 *
 *   2. d_nv != &d_inlineNv (d_nv heap-allocated by NodeBuilder): all
 *      d_nv children have their reference counts decremented, and
 *      d_nv is deallocated.
 */

#include "cvc5_private.h"

/* strong dependency; make sure node is included first */
#include "expr/node.h"

#ifndef CVC5__NODE_BUILDER_H
#define CVC5__NODE_BUILDER_H

#include <iostream>
#include <vector>

#include "base/check.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/node_value.h"
#include "expr/type_node.h"

namespace cvc5::internal {

class NodeManager;

/**
 * The NodeBuilder.
 */
class NodeBuilder {
  friend std::ostream& operator<<(std::ostream& out, const NodeBuilder& nb);

  constexpr static size_t default_nchild_thresh = 10;

 public:
  NodeBuilder();
  NodeBuilder(Kind k);
  NodeBuilder(NodeManager* nm);
  NodeBuilder(NodeManager* nm, Kind k);
  NodeBuilder(const NodeBuilder& nb);

  ~NodeBuilder();

  /** Get the kind of this Node-under-construction. */
  Kind getKind() const;

  /** Get the kind of this Node-under-construction. */
  kind::MetaKind getMetaKind() const;

  /** Get the current number of children of this Node-under-construction. */
  unsigned getNumChildren() const;

  /**
   * Access to the operator of this Node-under-construction.  Only
   * allowed if this NodeBuilder is unused, and has a defined kind
   * that is of PARAMETERIZED metakind.
   */
  Node getOperator() const;

  /**
   * Access to children of this Node-under-construction.  Only allowed
   * if this NodeBuilder is unused and has a defined kind.
   */
  Node getChild(int i) const;

  /** Access to children of this Node-under-construction. */
  Node operator[](int i) const;

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
  NodeBuilder& operator<<(const Kind& k);

  /**
   * If this Node-under-construction has a Kind set, collapse it and
   * append the given Node as a child.  Otherwise, simply append.
   */
  NodeBuilder& operator<<(TNode n);

  /**
   * If this Node-under-construction has a Kind set, collapse it and
   * append the given Node as a child.  Otherwise, simply append.
   */
  NodeBuilder& operator<<(TypeNode n);

  /** Append a sequence of children to this TypeNode-under-construction. */
  NodeBuilder& append(const std::vector<TypeNode>& children);

  /** Append a sequence of children to this Node-under-construction. */
  template <bool ref_count>
  inline NodeBuilder& append(
      const std::vector<NodeTemplate<ref_count> >& children)
  {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    return append(children.begin(), children.end());
  }

  /** Append a sequence of children to this Node-under-construction. */
  template <class Iterator>
  NodeBuilder& append(const Iterator& begin, const Iterator& end)
  {
    Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                         "attempt to access it after conversion";
    for(Iterator i = begin; i != end; ++i) {
      append(*i);
    }
    return *this;
  }

  /** Append a child to this Node-under-construction. */
  NodeBuilder& append(TNode n);

  /** Append a child to this Node-under-construction. */
  NodeBuilder& append(const TypeNode& typeNode);

  /** Construct the Node out of the node builder */
  Node constructNode();

  /** Construct a Node on the heap out of the node builder */
  Node* constructNodePtr();

  /** Construction of the TypeNode out of the node builder */
  TypeNode constructTypeNode();

  // two versions, so we can support extraction from (const)
  // NodeBuilders which are temporaries appearing as rvalues
  operator Node();

  // similarly for TypeNode
  operator TypeNode();

 private:
  void internalCopy(const NodeBuilder& nb);

  /**
   * Returns whether or not this NodeBuilder has been "used"---i.e.,
   * whether a Node has been extracted with operator Node().
   * Internally, this state is represented by d_nv pointing to NULL.
   */
  bool isUsed() const;

  /**
   * Set this NodeBuilder to the `used' state.
   */
  void setUsed();

  /**
   * Set this NodeBuilder to the `unused' state.  Should only be done
   * from clear().
   */
  void setUnused();

  /**
   * Returns true if d_nv is *not* the "in-line" one (it was
   * heap-allocated by this class).
   */
  bool nvIsAllocated() const;

  /**
   * Returns true if adding a child requires (re)allocation of d_nv
   * first.
   */
  bool nvNeedsToBeAllocated() const;

  /**
   * (Re)allocate d_nv using a default grow factor.  Ensure that child
   * pointers are copied into the new buffer, and if the "inline"
   * NodeValue is evacuated, make sure its children won't be
   * double-decremented later (on destruction/clear).
   */
  void realloc();

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
  void allocateNvIfNecessaryForAppend();

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
  void crop();

  /** Construct the node value out of the node builder */
  expr::NodeValue* constructNV();

#ifdef CVC5_DEBUG
  // Throws a TypeCheckingExceptionPrivate on a failure.
  void maybeCheckType(const TNode n) const;
#else  /* CVC5_DEBUG */
  // Do nothing if not in debug mode.
  inline void maybeCheckType(const TNode n) const {}
#endif /* CVC5_DEBUG */

  // used by convenience node builders
  NodeBuilder& collapseTo(Kind k);

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
  expr::NodeValue* d_inlineNvChildSpace[default_nchild_thresh];

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
}; /* class NodeBuilder */

// Sometimes it's useful for debugging to output a NodeBuilder that
// isn't yet a Node..
std::ostream& operator<<(std::ostream& out, const NodeBuilder& nb);

}  // namespace cvc5::internal

#endif /* CVC5__NODE_BUILDER_H */
