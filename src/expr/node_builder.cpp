/******************************************************************************
 * Top contributors (to current version):
 *   Andres Noetzli, Morgan Deters, Mathias Preiner
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
 */

#include "expr/node_builder.h"

#include <memory>

namespace cvc5::internal {

NodeBuilder::NodeBuilder()
    : d_nv(&d_inlineNv),
      d_nm(NodeManager::currentNM()),
      d_nvMaxChildren(default_nchild_thresh)
{
  d_inlineNv.d_id = 0;
  d_inlineNv.d_rc = 0;
  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(kind::UNDEFINED_KIND);
  d_inlineNv.d_nchildren = 0;
}

NodeBuilder::NodeBuilder(Kind k)
    : d_nv(&d_inlineNv),
      d_nm(NodeManager::currentNM()),
      d_nvMaxChildren(default_nchild_thresh)
{
  Assert(k != kind::NULL_EXPR && k != kind::UNDEFINED_KIND)
      << "illegal Node-building kind";

  d_inlineNv.d_id = 1;  // have a kind already
  d_inlineNv.d_rc = 0;
  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(k);
  d_inlineNv.d_nchildren = 0;
}

NodeBuilder::NodeBuilder(NodeManager* nm)
    : d_nv(&d_inlineNv), d_nm(nm), d_nvMaxChildren(default_nchild_thresh)
{
  d_inlineNv.d_id = 0;
  d_inlineNv.d_rc = 0;
  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(kind::UNDEFINED_KIND);
  d_inlineNv.d_nchildren = 0;
}

NodeBuilder::NodeBuilder(NodeManager* nm, Kind k)
    : d_nv(&d_inlineNv), d_nm(nm), d_nvMaxChildren(default_nchild_thresh)
{
  Assert(k != kind::NULL_EXPR && k != kind::UNDEFINED_KIND)
      << "illegal Node-building kind";

  d_inlineNv.d_id = 1;  // have a kind already
  d_inlineNv.d_rc = 0;
  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(k);
  d_inlineNv.d_nchildren = 0;
}

NodeBuilder::NodeBuilder(const NodeBuilder& nb)
    : d_nv(&d_inlineNv), d_nm(nb.d_nm), d_nvMaxChildren(default_nchild_thresh)
{
  d_inlineNv.d_id = nb.d_nv->d_id;
  d_inlineNv.d_rc = 0;
  d_inlineNv.d_kind = nb.d_nv->d_kind;
  d_inlineNv.d_nchildren = 0;

  internalCopy(nb);
}

NodeBuilder::~NodeBuilder()
{
  if (CVC5_PREDICT_FALSE(nvIsAllocated()))
  {
    dealloc();
  }
  else if (CVC5_PREDICT_FALSE(!isUsed()))
  {
    decrRefCounts();
  }
}

Kind NodeBuilder::getKind() const
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  return d_nv->getKind();
}

kind::MetaKind NodeBuilder::getMetaKind() const
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  Assert(getKind() != kind::UNDEFINED_KIND)
      << "The metakind of a NodeBuilder is undefined "
         "until a Kind is set";
  return d_nv->getMetaKind();
}

unsigned NodeBuilder::getNumChildren() const
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  Assert(getKind() != kind::UNDEFINED_KIND)
      << "The number of children of a NodeBuilder is undefined "
         "until a Kind is set";
  return d_nv->getNumChildren();
}

Node NodeBuilder::getOperator() const
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  Assert(getKind() != kind::UNDEFINED_KIND)
      << "NodeBuilder operator access is not permitted "
         "until a Kind is set";
  Assert(getMetaKind() == kind::metakind::PARAMETERIZED)
      << "NodeBuilder operator access is only permitted "
         "on parameterized kinds, not `"
      << getKind() << "'";
  return Node(d_nv->getOperator());
}

Node NodeBuilder::getChild(int i) const
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  Assert(getKind() != kind::UNDEFINED_KIND)
      << "NodeBuilder child access is not permitted "
         "until a Kind is set";
  Assert(i >= 0 && unsigned(i) < d_nv->getNumChildren())
      << "index out of range for NodeBuilder::getChild()";
  return Node(d_nv->getChild(i));
}

Node NodeBuilder::operator[](int i) const { return getChild(i); }

void NodeBuilder::clear(Kind k)
{
  Assert(k != kind::NULL_EXPR) << "illegal Node-building clear kind";

  if (CVC5_PREDICT_FALSE(nvIsAllocated()))
  {
    dealloc();
  }
  else if (CVC5_PREDICT_FALSE(!isUsed()))
  {
    decrRefCounts();
  }
  else
  {
    setUnused();
  }

  d_inlineNv.d_kind = expr::NodeValue::kindToDKind(k);
  for (expr::NodeValue::nv_iterator i = d_inlineNv.nv_begin();
       i != d_inlineNv.nv_end();
       ++i)
  {
    (*i)->dec();
  }
  d_inlineNv.d_nchildren = 0;
  // keep track of whether or not we hvae a kind already
  d_inlineNv.d_id = (k == kind::UNDEFINED_KIND) ? 0 : 1;
}

NodeBuilder& NodeBuilder::operator<<(const Kind& k)
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  Assert(getKind() == kind::UNDEFINED_KIND || d_nv->d_id == 0)
      << "can't redefine the Kind of a NodeBuilder";
  Assert(d_nv->d_id == 0)
      << "internal inconsistency with NodeBuilder: d_id != 0";
  AssertArgument(
      k != kind::UNDEFINED_KIND && k != kind::NULL_EXPR && k < kind::LAST_KIND,
      k,
      "illegal node-building kind");
  // This test means: we didn't have a Kind at the beginning (on
  // NodeBuilder construction or at the last clear()), but we do
  // now.  That means we appended a Kind with operator<<(Kind),
  // which now (lazily) we'll collapse.
  if (CVC5_PREDICT_FALSE(d_nv->d_id == 0 && getKind() != kind::UNDEFINED_KIND))
  {
    Node n2 = operator Node();
    clear();
    append(n2);
  }
  else if (d_nv->d_nchildren == 0)
  {
    d_nv->d_id = 1;  // remember that we had a kind from the start
  }
  d_nv->d_kind = expr::NodeValue::kindToDKind(k);
  return *this;
}

NodeBuilder& NodeBuilder::operator<<(TNode n)
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  // This test means: we didn't have a Kind at the beginning (on
  // NodeBuilder construction or at the last clear()), but we do
  // now.  That means we appended a Kind with operator<<(Kind),
  // which now (lazily) we'll collapse.
  if (CVC5_PREDICT_FALSE(d_nv->d_id == 0 && getKind() != kind::UNDEFINED_KIND))
  {
    Node n2 = operator Node();
    clear();
    append(n2);
  }
  return append(n);
}

NodeBuilder& NodeBuilder::operator<<(TypeNode n)
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  // This test means: we didn't have a Kind at the beginning (on
  // NodeBuilder construction or at the last clear()), but we do
  // now.  That means we appended a Kind with operator<<(Kind),
  // which now (lazily) we'll collapse.
  if (CVC5_PREDICT_FALSE(d_nv->d_id == 0 && getKind() != kind::UNDEFINED_KIND))
  {
    Node n2 = operator Node();
    clear();
    append(n2);
  }
  return append(n);
}

NodeBuilder& NodeBuilder::append(const std::vector<TypeNode>& children)
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  return append(children.begin(), children.end());
}

NodeBuilder& NodeBuilder::append(TNode n)
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  Assert(!n.isNull()) << "Cannot use NULL Node as a child of a Node";
  if (n.getKind() == kind::BUILTIN)
  {
    return *this << NodeManager::operatorToKind(n);
  }
  allocateNvIfNecessaryForAppend();
  expr::NodeValue* nv = n.d_nv;
  nv->inc();
  d_nv->d_children[d_nv->d_nchildren++] = nv;
  Assert(d_nv->d_nchildren <= d_nvMaxChildren);
  return *this;
}

NodeBuilder& NodeBuilder::append(const TypeNode& typeNode)
{
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

void NodeBuilder::realloc(size_t toSize)
{
  AlwaysAssert(toSize > d_nvMaxChildren)
      << "attempt to realloc() a NodeBuilder to a smaller/equal size!";
  Assert(toSize < (static_cast<size_t>(1) << expr::NodeValue::NBITS_NCHILDREN))
      << "attempt to realloc() a NodeBuilder to size " << toSize
      << " (beyond hard limit of " << expr::NodeValue::MAX_CHILDREN << ")";

  if (CVC5_PREDICT_FALSE(nvIsAllocated()))
  {
    // Ensure d_nv is not modified on allocation failure
    expr::NodeValue* newBlock = (expr::NodeValue*)std::realloc(
        d_nv, sizeof(expr::NodeValue) + (sizeof(expr::NodeValue*) * toSize));
    if (newBlock == nullptr)
    {
      // In this case, d_nv was NOT freed.  If we throw, the
      // deallocation should occur on destruction of the NodeBuilder.
      throw std::bad_alloc();
    }
    d_nvMaxChildren = toSize;
    Assert(d_nvMaxChildren == toSize);  // overflow check
    // Here, the copy (between two heap-allocated buffers) has already
    // been done for us by the std::realloc().
    d_nv = newBlock;
  }
  else
  {
    // Ensure d_nv is not modified on allocation failure
    expr::NodeValue* newBlock = (expr::NodeValue*)std::malloc(
        sizeof(expr::NodeValue) + (sizeof(expr::NodeValue*) * toSize));
    if (newBlock == nullptr)
    {
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

void NodeBuilder::dealloc()
{
  Assert(nvIsAllocated())
      << "Internal error: NodeBuilder: dealloc() called without a "
         "private NodeBuilder-allocated buffer";

  for (expr::NodeValue::nv_iterator i = d_nv->nv_begin(); i != d_nv->nv_end();
       ++i)
  {
    (*i)->dec();
  }

  free(d_nv);
  d_nv = &d_inlineNv;
  d_nvMaxChildren = default_nchild_thresh;
}

void NodeBuilder::decrRefCounts()
{
  Assert(!nvIsAllocated())
      << "Internal error: NodeBuilder: decrRefCounts() called with a "
         "private NodeBuilder-allocated buffer";

  for (expr::NodeValue::nv_iterator i = d_inlineNv.nv_begin();
       i != d_inlineNv.nv_end();
       ++i)
  {
    (*i)->dec();
  }

  d_inlineNv.d_nchildren = 0;
}

TypeNode NodeBuilder::constructTypeNode() { return TypeNode(constructNV()); }

Node NodeBuilder::constructNode()
{
  Node n(constructNV());
  maybeCheckType(n);
  return n;
}

Node* NodeBuilder::constructNodePtr()
{
  std::unique_ptr<Node> np(new Node(constructNV()));
  maybeCheckType(*np.get());
  return np.release();
}

NodeBuilder::operator Node() { return constructNode(); }

NodeBuilder::operator TypeNode() { return constructTypeNode(); }

expr::NodeValue* NodeBuilder::constructNV()
{
  Assert(!isUsed()) << "NodeBuilder is one-shot only; "
                       "attempt to access it after conversion";
  Assert(getKind() != kind::UNDEFINED_KIND)
      << "Can't make an expression of an undefined kind!";

  // NOTE: The comments in this function refer to the cases in the
  // file comments at the top of this file.

  // Case 0: If a VARIABLE
  if (getMetaKind() == kind::metakind::VARIABLE
      || getMetaKind() == kind::metakind::NULLARY_OPERATOR)
  {
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
    expr::NodeValue* nv =
        (expr::NodeValue*)std::malloc(sizeof(expr::NodeValue));
    if (nv == nullptr)
    {
      throw std::bad_alloc();
    }
    // there are no children, so we don't have to worry about
    // reference counts in this case.
    nv->d_nchildren = 0;
    nv->d_kind = d_nv->d_kind;
    nv->d_id = d_nm->d_nextId++;
    nv->d_rc = 0;
    setUsed();
    if (TraceIsOn("gc"))
    {
      Trace("gc") << "creating node value " << nv << " [" << nv->d_id << "]: ";
      nv->printAst(Trace("gc"));
      Trace("gc") << std::endl;
    }
    return nv;
  }

  // check that there are the right # of children for this kind
  Assert(getMetaKind() != kind::metakind::CONSTANT)
      << "Cannot make Nodes with NodeBuilder that have CONSTANT-kinded kinds";
  Assert(getNumChildren() >= kind::metakind::getMinArityForKind(getKind()))
      << "Nodes with kind `" << getKind() << "` must have at least "
      << kind::metakind::getMinArityForKind(getKind())
      << " children (the one under "
         "construction has "
      << getNumChildren() << ")";
  Assert(getNumChildren() <= kind::metakind::getMaxArityForKind(getKind()))
      << "Nodes with kind `" << getKind() << "` must have at most "
      << kind::metakind::getMaxArityForKind(getKind())
      << " children (the one under "
         "construction has "
      << getNumChildren() << ")";

  // Implementation differs depending on whether the NodeValue was
  // malloc'ed or not and whether or not it's in the already-been-seen
  // NodeManager pool of Nodes.  See implementation notes at the top
  // of this file.

  if (CVC5_PREDICT_TRUE(!nvIsAllocated()))
  {
    /** Case 1.  d_nv points to d_inlineNv: it is the backing store
     ** allocated "inline" in this NodeBuilder. **/

    // Lookup the expression value in the pool we already have
    expr::NodeValue* poolNv = d_nm->poolLookup(&d_inlineNv);
    // If something else is there, we reuse it
    if (poolNv != nullptr)
    {
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
    }
    else
    {
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
      expr::NodeValue* nv = (expr::NodeValue*)std::malloc(
          sizeof(expr::NodeValue)
          + (sizeof(expr::NodeValue*) * d_inlineNv.d_nchildren));
      if (nv == nullptr)
      {
        throw std::bad_alloc();
      }
      nv->d_nchildren = d_inlineNv.d_nchildren;
      nv->d_kind = d_inlineNv.d_kind;
      nv->d_id = d_nm->d_nextId++;
      nv->d_rc = 0;

      std::copy(d_inlineNv.d_children,
                d_inlineNv.d_children + d_inlineNv.d_nchildren,
                nv->d_children);

      d_inlineNv.d_nchildren = 0;
      setUsed();

      // poolNv = nv;
      d_nm->poolInsert(nv);
      if (TraceIsOn("gc"))
      {
        Trace("gc") << "creating node value " << nv << " [" << nv->d_id
                    << "]: ";
        nv->printAst(Trace("gc"));
        Trace("gc") << std::endl;
      }
      return nv;
    }
  }
  else
  {
    /** Case 2. d_nv does NOT point to d_inlineNv: it is a new, larger
     ** buffer that was heap-allocated by this NodeBuilder. **/

    // Lookup the expression value in the pool we already have (with insert)
    expr::NodeValue* poolNv = d_nm->poolLookup(d_nv);
    // If something else is there, we reuse it
    if (poolNv != nullptr)
    {
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
    }
    else
    {
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
      nv->d_id = d_nm->d_nextId++;
      d_nv = &d_inlineNv;
      d_nvMaxChildren = default_nchild_thresh;
      setUsed();

      // poolNv = nv;
      d_nm->poolInsert(nv);
      Trace("gc") << "creating node value " << nv << " [" << nv->d_id
                  << "]: " << *nv << "\n";
      return nv;
    }
  }
}

void NodeBuilder::internalCopy(const NodeBuilder& nb)
{
  if (nb.isUsed())
  {
    setUsed();
    return;
  }

  bool realloced CVC5_UNUSED = false;
  if (nb.d_nvMaxChildren > d_nvMaxChildren)
  {
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

  for (expr::NodeValue::nv_iterator i = d_nv->nv_begin(); i != d_nv->nv_end();
       ++i)
  {
    (*i)->inc();
  }
}

#ifdef CVC5_DEBUG
inline void NodeBuilder::maybeCheckType(const TNode n) const
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
#endif /* CVC5_DEBUG */

bool NodeBuilder::isUsed() const { return CVC5_PREDICT_FALSE(d_nv == nullptr); }

void NodeBuilder::setUsed()
{
  Assert(!isUsed()) << "Internal error: bad `used' state in NodeBuilder!";
  Assert(d_inlineNv.d_nchildren == 0
         && d_nvMaxChildren == default_nchild_thresh)
      << "Internal error: bad `inline' state in NodeBuilder!";
  d_nv = nullptr;
}

void NodeBuilder::setUnused()
{
  Assert(isUsed()) << "Internal error: bad `used' state in NodeBuilder!";
  Assert(d_inlineNv.d_nchildren == 0
         && d_nvMaxChildren == default_nchild_thresh)
      << "Internal error: bad `inline' state in NodeBuilder!";
  d_nv = &d_inlineNv;
}

bool NodeBuilder::nvIsAllocated() const
{
  return CVC5_PREDICT_FALSE(d_nv != &d_inlineNv)
         && CVC5_PREDICT_TRUE(d_nv != nullptr);
}

bool NodeBuilder::nvNeedsToBeAllocated() const
{
  return CVC5_PREDICT_FALSE(d_nv->d_nchildren == d_nvMaxChildren);
}

void NodeBuilder::realloc()
{
  size_t newSize = 2 * size_t(d_nvMaxChildren);
  size_t hardLimit = expr::NodeValue::MAX_CHILDREN;
  realloc(CVC5_PREDICT_FALSE(newSize > hardLimit) ? hardLimit : newSize);
}

void NodeBuilder::allocateNvIfNecessaryForAppend()
{
  if (CVC5_PREDICT_FALSE(nvNeedsToBeAllocated()))
  {
    realloc();
  }
}

void NodeBuilder::crop()
{
  if (CVC5_PREDICT_FALSE(nvIsAllocated())
      && CVC5_PREDICT_TRUE(d_nvMaxChildren > d_nv->d_nchildren))
  {
    // Ensure d_nv is not modified on allocation failure
    expr::NodeValue* newBlock = (expr::NodeValue*)std::realloc(
        d_nv,
        sizeof(expr::NodeValue)
            + (sizeof(expr::NodeValue*) * d_nv->d_nchildren));
    if (newBlock == nullptr)
    {
      // In this case, d_nv was NOT freed.  If we throw, the
      // deallocation should occur on destruction of the
      // NodeBuilder.
      throw std::bad_alloc();
    }
    d_nv = newBlock;
    d_nvMaxChildren = d_nv->d_nchildren;
  }
}

NodeBuilder& NodeBuilder::collapseTo(Kind k)
{
  AssertArgument(
      k != kind::UNDEFINED_KIND && k != kind::NULL_EXPR && k < kind::LAST_KIND,
      k,
      "illegal collapsing kind");

  if (getKind() != k)
  {
    Node n = operator Node();
    clear();
    d_nv->d_kind = expr::NodeValue::kindToDKind(k);
    d_nv->d_id = 1;  // have a kind already
    return append(n);
  }
  return *this;
}

std::ostream& operator<<(std::ostream& out, const NodeBuilder& nb)
{
  return out << *nb.d_nv;
}

}  // namespace cvc5::internal
