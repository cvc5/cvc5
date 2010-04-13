/*********************                                                        */
/** node_manager.h
 ** Original author: mdeters
 ** Major contributors: cconway
 ** Minor contributors (to current version): taking, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A manager for Nodes.
 **
 ** Reviewed by Chris Conway, Apr 5 2010 (bug #65).
 **/

#include "cvc4_private.h"

/* circular dependency; force node.h first */
#include "expr/attribute.h"
#include "expr/node.h"

#ifndef __CVC4__NODE_MANAGER_H
#define __CVC4__NODE_MANAGER_H

#include <vector>
#include <string>
#include <ext/hash_set>

#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/expr.h"
#include "expr/node_value.h"
#include "context/context.h"
#include "expr/type.h"

namespace CVC4 {

namespace expr {

// Definition of an attribute for the variable name.
// TODO: hide this attribute behind a NodeManager interface.
namespace attr {
  struct VarNameTag {};
}/* CVC4::expr::attr namespace */

typedef expr::Attribute<attr::VarNameTag, std::string> VarNameAttr;

}/* CVC4::expr namespace */

class NodeManager {
  template <class Builder> friend class CVC4::NodeBuilderBase;
  friend class NodeManagerScope;
  friend class expr::NodeValue;

  typedef __gnu_cxx::hash_set<expr::NodeValue*,
                              expr::NodeValuePoolHashFcn,
                              expr::NodeValuePoolEq> NodeValuePool;
  typedef __gnu_cxx::hash_set<expr::NodeValue*,
                              expr::NodeValueIDHashFunction,
                              expr::NodeValueEq> ZombieSet;

  static __thread NodeManager* s_current;

  NodeValuePool d_nodeValuePool;

  expr::attr::AttributeManager d_attrManager;

  /**
   * The node value we're currently freeing.  This unique node value
   * is permitted to have outstanding TNodes to it (in "soft"
   * contexts, like as a key in attribute tables), even though
   * normally it's an error to have a TNode to a node value with a
   * reference count of 0.  Being "under deletion" also enables
   * assertions that inc() is not called on it.  (A poorly-behaving
   * attribute cleanup function could otherwise create a "Node" that
   * points to the node value that is in the process of being deleted,
   * springing it back to life.)
   */
  expr::NodeValue* d_nodeUnderDeletion;

  /**
   * True iff we are in reclaimZombies().  This avoids unnecessary
   * recursion; a NodeValue being deleted might zombify other
   * NodeValues, but these shouldn't trigger a (recursive) call to
   * reclaimZombies().
   */
  bool d_reclaiming;

  /**
   * The set of zombie nodes.  We may want to revisit this design, as
   * we might like to delete nodes in least-recently-used order.  But
   * we also need to avoid processing a zombie twice.
   */
  ZombieSet d_zombies;

  /**
   * A set of operator singletons (w.r.t.  to this NodeManager
   * instance) for operators.  Conceptually, Nodes with kind, say,
   * PLUS, are APPLYs of a PLUS operator to arguments.  This array
   * holds the set of operators for these things.  A PLUS operator is
   * a Node with kind "BUILTIN", and if you call
   * plusOperator->getConst<CVC4::Kind>(), you get kind::PLUS back.
   */
  Node d_operators[kind::LAST_KIND];

  /**
   * Look up a NodeValue in the pool associated to this NodeManager.
   * The NodeValue argument need not be a "completely-constructed"
   * NodeValue.  In particular, "non-inlined" constants are permitted
   * (see below).
   *
   * For non-CONSTANT metakinds, nv's d_kind and d_nchildren should be
   * correctly set, and d_children[0..n-1] should be valid (extant)
   * NodeValues for lookup.
   *
   * For CONSTANT metakinds, nv's d_kind should be set correctly.
   * Normally a CONSTANT would have d_nchildren == 0 and the constant
   * value inlined in the d_children space.  However, here we permit
   * "non-inlined" NodeValues to avoid unnecessary copying.  For
   * these, d_nchildren == 1, and d_nchildren is a pointer to the
   * constant value.
   *
   * The point of this complex design is to permit efficient lookups
   * (without fully constructing a NodeValue).  In the case that the
   * argument is not fully constructed, and this function returns
   * NULL, the caller should fully construct an equivalent one before
   * calling poolInsert().  NON-FULLY-CONSTRUCTED NODEVALUES are not
   * permitted in the pool!
   */
  inline expr::NodeValue* poolLookup(expr::NodeValue* nv) const;

  /**
   * Insert a NodeValue into the NodeManager's pool.
   *
   * It is an error to insert a NodeValue already in the pool.
   * Enquire first with poolLookup().
   */
  inline void poolInsert(expr::NodeValue* nv);

  /**
   * Remove a NodeValue from the NodeManager's pool.
   *
   * It is an error to request the removal of a NodeValue from the
   * pool that is not in the pool.
   */
  inline void poolRemove(expr::NodeValue* nv);

  /**
   * Determine if nv is currently being deleted by the NodeManager.
   */
  inline bool isCurrentlyDeleting(const expr::NodeValue* nv) const {
    return d_nodeUnderDeletion == nv;
  }

  /**
   * Register a NodeValue as a zombie.
   */
  inline void markForDeletion(expr::NodeValue* nv) {
    Assert(nv->d_rc == 0);

    // if d_reclaiming is set, make sure we don't call
    // reclaimZombies(), because it's already running.
    Debug("gc") << "zombifying node value " << nv
                << " [" << nv->d_id << "]: " << *nv
                << (d_reclaiming ? " [CURRENTLY-RECLAIMING]" : "")
                << std::endl;
    d_zombies.insert(nv);// FIXME multithreading

    if(!d_reclaiming) {// FIXME multithreading
      // for now, collect eagerly.  can add heuristic here later..
      reclaimZombies();
    }
  }

  /**
   * Reclaim all zombies.
   */
  void reclaimZombies();

  /**
   * This template gives a mechanism to stack-allocate a NodeValue
   * with enough space for N children (where N is a compile-time
   * constant).  You use it like this:
   *
   *   NVStorage<4> nvStorage;
   *   NodeValue& nvStack = reinterpret_cast<NodeValue&>(nvStorage);
   *
   * ...and then you can use nvStack as a NodeValue that you know has
   * room for 4 children.
   */
  template <size_t N>
  struct NVStorage {
    expr::NodeValue nv;
    expr::NodeValue* child[N];
  };/* struct NodeManager::NVStorage<N> */

  // attribute tags
  struct TypeTag {};
  struct AtomicTag {};

  // NodeManager's attributes.  These aren't exposed outside of this
  // class; use the getters.
  typedef expr::ManagedAttribute<TypeTag,
                                 CVC4::Type*,
                                 expr::attr::TypeCleanupStrategy> TypeAttr;
  typedef expr::Attribute<AtomicTag, bool> AtomicAttr;

  /**
   * Returns true if this node is atomic (has no more Boolean
   * structure).  This is the NodeValue version for NodeManager's
   * internal use.  There's a public version of this function below
   * that takes a TNode.
   * @param nv the node to check for atomicity
   * @return true if atomic
   */
  inline bool isAtomic(expr::NodeValue* nv) const {
    // The kindCanBeAtomic() and metakind checking are just optimizations
    // (to avoid the hashtable lookup).  We assume that all nodes have
    // the atomic attribute pre-computed and set at their time of
    // creation.  This is because:
    // (1) it's super cheap to do it bottom-up.
    // (2) if we computed it lazily, we'd need a second attribute to
    //     tell us whether we had computed it yet or not.
    // The pre-computation and registration occurs in poolInsert().
    AssertArgument(nv->getMetaKind() != kind::metakind::INVALID, *nv,
                   "NodeManager::isAtomic() called on INVALID node (%s)",
                   kind::kindToString(nv->getKind()).c_str());
    return
      nv->getMetaKind() == kind::metakind::VARIABLE ||
      nv->getMetaKind() == kind::metakind::CONSTANT ||
      ( kind::kindCanBeAtomic(nv->getKind()) &&
        getAttribute(nv, AtomicAttr()) );
  }

public:

  NodeManager(context::Context* ctxt);
  ~NodeManager();

  /** The node manager in the current context. */
  static NodeManager* currentNM() { return s_current; }

  // general expression-builders

  /** Create a node with no children. */
  Node mkNode(Kind kind);

  /** Create a node with one child. */
  Node mkNode(Kind kind, TNode child1);

  /** Create a node with two children. */
  Node mkNode(Kind kind, TNode child1, TNode child2);

  /** Create a node with three children. */
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3);

  /** Create a node with four children. */
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3,
              TNode child4);

  /** Create a node with five children. */
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3,
              TNode child4, TNode child5);

  /** Create a node with an arbitrary number of children. */
  template <bool ref_count>
  Node mkNode(Kind kind, const std::vector<NodeTemplate<ref_count> >& children);

  /**
   * Create a variable with the given name and type.  NOTE that no
   * lookup is done on the name.  If you mkVar("a", type) and then
   * mkVar("a", type) again, you have two variables.
   */
  Node mkVar(const std::string& name, Type* type);

  /** Create a variable with the given type. */
  Node mkVar(Type* type);

  /**
   * Create a constant of type T.  It will have the appropriate
   * CONST_* kind defined for T.
   */
  template <class T>
  Node mkConst(const T&);

  /**
   * Determine whether Nodes of a particular Kind have operators.
   * @returns true if Nodes of Kind k have operators.
   */
  static inline bool hasOperator(Kind k);

  /**
   * Get the (singleton) operator of an OPERATOR-kinded kind.  The
   * returned node n will have kind BUILTIN, and calling
   * n.getConst<CVC4::Kind>() will yield k.
   */
  inline TNode operatorOf(Kind k) {
    AssertArgument( kind::metaKindOf(k) == kind::metakind::OPERATOR, k,
                    "Kind is not an OPERATOR-kinded kind "
                    "in NodeManager::operatorOf()" );
    return d_operators[k];
  }

  /**
   * Retrieve an attribute for a node.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to retrieve.
   * @returns the attribute, if set, or a default-constructed
   * <code>AttrKind::value_type</code> if not.
   */
  template <class AttrKind>
  inline typename AttrKind::value_type getAttribute(expr::NodeValue* nv,
                                                    const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a node.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to check
   * @returns <code>true</code> iff <code>attr</code> is set for
   * <code>nv</code>.
   */
  template <class AttrKind>
  inline bool hasAttribute(expr::NodeValue* nv,
                           const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a node, and, if so,
   * retrieve it.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to check
   * @param value a reference to an object of the attribute's value type.
   * <code>value</code> will be set to the value of the attribute, if it is
   * set for <code>nv</code>; otherwise, it will be set to the default
   * value of the attribute.
   * @returns <code>true</code> iff <code>attr</code> is set for
   * <code>nv</code>.
   */
  template <class AttrKind>
  inline bool getAttribute(expr::NodeValue* nv,
                           const AttrKind& attr,
                           typename AttrKind::value_type& value) const;

  /**
   * Set an attribute for a node.  If the node doesn't have the
   * attribute, this function assigns one.  If the node has one, this
   * overwrites it.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to set
   * @param value the value of <code>attr</code> for <code>nv</code>
   */
  template <class AttrKind>
  inline void setAttribute(expr::NodeValue* nv,
                           const AttrKind& attr,
                           const typename AttrKind::value_type& value);

  /**
   * Retrieve an attribute for a TNode.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to retrieve.
   * @returns the attribute, if set, or a default-constructed
   * <code>AttrKind::value_type</code> if not.
   */
  template <class AttrKind>
  inline typename AttrKind::value_type 
  getAttribute(TNode n, const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a TNode.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to check
   * @returns <code>true</code> iff <code>attr</code> is set for <code>n</code>.
   */
  template <class AttrKind>
  inline bool hasAttribute(TNode n,
                           const AttrKind& attr) const;

  /**
   * Check whether an attribute is set for a TNode and, if so, retieve
   * it.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to check
   * @param value a reference to an object of the attribute's value type.
   * <code>value</code> will be set to the value of the attribute, if it is
   * set for <code>nv</code>; otherwise, it will be set to the default value of
   * the attribute.
   * @returns <code>true</code> iff <code>attr</code> is set for <code>n</code>.
   */
  template <class AttrKind>
  inline bool getAttribute(TNode n,
                           const AttrKind& attr,
                           typename AttrKind::value_type& value) const;

  /**
   * Set an attribute for a node.  If the node doesn't have the
   * attribute, this function assigns one.  If the node has one, this
   * overwrites it.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to set
   * @param value the value of <code>attr</code> for <code>n</code>
   */
  template <class AttrKind>
  inline void setAttribute(TNode n,
                           const AttrKind& attr,
                           const typename AttrKind::value_type& value);

  /** Get the (singleton) type for booleans. */
  inline BooleanType* booleanType() const {
    return BooleanType::getInstance();
  }

  /** Get the (singleton) type for sorts. */
  inline KindType* kindType() const {
    return KindType::getInstance();
  }

  /**
   * Make a function type from domain to range.
   *
   * @param domain the domain type
   * @param range the range type
   * @returns the functional type domain -> range
   */
  inline FunctionType* mkFunctionType(Type* domain, Type* range) const;

  /**
   * Make a function type with input types from
   * argTypes. <code>argTypes</code> must have at least one element.
   *
   * @param argTypes the domain is a tuple (argTypes[0], ..., argTypes[n])
   * @param range the range type
   * @returns the functional type (argTypes[0], ..., argTypes[n]) -> range
   */
  inline FunctionType* mkFunctionType(const std::vector<Type*>& argTypes,
                                      Type* range) const;

  /**
   * Make a function type with input types from
   * <code>sorts[0..sorts.size()-2]</code> and result type
   * <code>sorts[sorts.size()-1]</code>. <code>sorts</code> must have
   * at least 2 elements.
   */
  inline FunctionType* mkFunctionType(const std::vector<Type*>& sorts) const;

  /**
   * Make a predicate type with input types from
   * <code>sorts</code>. The result with be a function type with range
   * <code>BOOLEAN</code>. <code>sorts</code> must have at least one
   * element.
   */
  inline FunctionType* mkPredicateType(const std::vector<Type*>& sorts) const;

  /** Make a new sort with the given name. */
  inline Type* mkSort(const std::string& name) const;

  /** Get the type for the given node.
   *
   * TODO: Does this call compute the type if it's not already available?
   */
  inline Type* getType(TNode n) const;

  /**
   * Returns true if this node is atomic (has no more Boolean structure)
   * @param n the node to check for atomicity
   * @return true if atomic
   */
  inline bool isAtomic(TNode n) const {
    return isAtomic(n.d_nv);
  }
};

/**
 * This class changes the "current" thread-global
 * <code>NodeManager</code> when it is created and reinstates the
 * previous thread-global <code>NodeManager</code> when it is
 * destroyed, effectively maintaining a set of nested
 * <code>NodeManager</code> scopes.  This is especially useful on
 * public-interface calls into the CVC4 library, where CVC4's notion
 * of the "current" <code>NodeManager</code> should be set to match
 * the calling context.  See, for example, the implementations of
 * public calls in the <code>ExprManager</code> and
 * <code>SmtEngine</code> classes.
 *
 * The client must be careful to create and destroy
 * <code>NodeManagerScope</code> objects in a well-nested manner (such
 * as on the stack). You may create a <code>NodeManagerScope</code>
 * with <code>new</code> and destroy it with <code>delete</code>, or
 * place it as a data member of an object that is, but if the scope of
 * these <code>new</code>/<code>delete</code> pairs isn't properly
 * maintained, the incorrect "current" <code>NodeManager</code>
 * pointer may be restored after a delete.
 */
class NodeManagerScope {
  /** The old NodeManager, to be restored on destruction. */
  NodeManager *d_oldNodeManager;

public:

  NodeManagerScope(NodeManager* nm) : d_oldNodeManager(NodeManager::s_current) {
    NodeManager::s_current = nm;
    Debug("current") << "node manager scope: "
                     << NodeManager::s_current << "\n";
  }

  ~NodeManagerScope() {
    NodeManager::s_current = d_oldNodeManager;
    Debug("current") << "node manager scope: "
                     << "returning to " << NodeManager::s_current << "\n";
  }
};

/**
 * Creates a <code>NodeManagerScope</code> with the underlying
 * <code>NodeManager</code> of a given <code>Expr</code> or
 * <code>ExprManager</code>.  The <code>NodeManagerScope</code> is
 * destroyed when the <code>ExprManagerScope</code> is destroyed. See
 * <code>NodeManagerScope</code> for more information.
 */
// NOTE: Here, it seems ExprManagerScope is redundant, since we have
// NodeManagerScope already.  However, without this class, we'd need
// Expr to be a friend of ExprManager, because in the implementation
// of Expr functions, it needs to set the current NodeManager
// correctly (and to do that it needs access to
// ExprManager::getNodeManager()).  So, we make ExprManagerScope a
// friend of ExprManager's, since its implementation is simple to
// read and understand (and verify that it doesn't do any mischief).
//
// ExprManager::getNodeManager() can't just be made public, since
// ExprManager is exposed to clients of the library and NodeManager is
// not.  Similarly, ExprManagerScope shouldn't go in expr_manager.h,
// since that's a public header.
class ExprManagerScope {
  NodeManagerScope d_nms;
public:
  inline ExprManagerScope(const Expr& e) :
    d_nms(e.getExprManager() == NULL
          ? NodeManager::currentNM()
          : e.getExprManager()->getNodeManager()) {
  }
  inline ExprManagerScope(const ExprManager& exprManager) :
    d_nms(exprManager.getNodeManager()) {
  }
};

template <class AttrKind>
inline typename AttrKind::value_type
NodeManager::getAttribute(expr::NodeValue* nv, const AttrKind&) const {
  return d_attrManager.getAttribute(nv, AttrKind());
}

template <class AttrKind>
inline bool NodeManager::hasAttribute(expr::NodeValue* nv,
                                      const AttrKind&) const {
  return d_attrManager.hasAttribute(nv, AttrKind());
}

template <class AttrKind>
inline bool
NodeManager::getAttribute(expr::NodeValue* nv, const AttrKind&,
                          typename AttrKind::value_type& ret) const {
  return d_attrManager.getAttribute(nv, AttrKind(), ret);
}

template <class AttrKind>
inline void
NodeManager::setAttribute(expr::NodeValue* nv, const AttrKind&,
                          const typename AttrKind::value_type& value) {
  d_attrManager.setAttribute(nv, AttrKind(), value);
}

template <class AttrKind>
inline typename AttrKind::value_type
NodeManager::getAttribute(TNode n, const AttrKind&) const {
  return d_attrManager.getAttribute(n.d_nv, AttrKind());
}

template <class AttrKind>
inline bool
NodeManager::hasAttribute(TNode n, const AttrKind&) const {
  return d_attrManager.hasAttribute(n.d_nv, AttrKind());
}

template <class AttrKind>
inline bool
NodeManager::getAttribute(TNode n, const AttrKind&,
                          typename AttrKind::value_type& ret) const {
  return d_attrManager.getAttribute(n.d_nv, AttrKind(), ret);
}

template <class AttrKind>
inline void
NodeManager::setAttribute(TNode n, const AttrKind&,
                          const typename AttrKind::value_type& value) {
  d_attrManager.setAttribute(n.d_nv, AttrKind(), value);
}

/** Make a function type from domain to range.
 * TODO: Function types should be unique for this manager. */
inline FunctionType* NodeManager::mkFunctionType(Type* domain,
                                                 Type* range) const {
  std::vector<Type*> argTypes;
  argTypes.push_back(domain);
  return new FunctionType(argTypes, range);
}

/** Make a function type with input types from argTypes.
 * TODO: Function types should be unique for this manager. */
inline FunctionType*
NodeManager::mkFunctionType(const std::vector<Type*>& argTypes,
                            Type* range) const {
  Assert( argTypes.size() > 0 );
  return new FunctionType(argTypes, range);
}

inline FunctionType*
NodeManager::mkFunctionType(const std::vector<Type*>& sorts) const {
  Assert( sorts.size() >= 2 );
  std::vector<Type*> argTypes(sorts);
  Type* rangeType = argTypes.back();
  argTypes.pop_back();
  return mkFunctionType(argTypes,rangeType);
}

inline FunctionType*
NodeManager::mkPredicateType(const std::vector<Type*>& sorts) const {
  Assert( sorts.size() >= 1 );
  return mkFunctionType(sorts,booleanType());
}

inline Type* NodeManager::mkSort(const std::string& name) const {
  return new SortType(name);
}

inline Type* NodeManager::getType(TNode n) const {
  return getAttribute(n, TypeAttr());
}

inline expr::NodeValue* NodeManager::poolLookup(expr::NodeValue* nv) const {
  NodeValuePool::const_iterator find = d_nodeValuePool.find(nv);
  if(find == d_nodeValuePool.end()) {
    return NULL;
  } else {
    return *find;
  }
}

inline void NodeManager::poolInsert(expr::NodeValue* nv) {
  Assert(d_nodeValuePool.find(nv) == d_nodeValuePool.end(),
         "NodeValue already in the pool!");
  d_nodeValuePool.insert(nv);// FIXME multithreading

  switch(nv->getMetaKind()) {
  case kind::metakind::INVALID:
  case kind::metakind::VARIABLE:
  case kind::metakind::CONSTANT:
    // nothing to do (don't bother setting the attribute, isAtomic()
    // on VARIABLEs and CONSTANTs is always true)
    break;

  case kind::metakind::OPERATOR:
  case kind::metakind::PARAMETERIZED:
    {
      // register this NodeValue as atomic or not; use nv_begin/end
      // because we need to consider the operator too in the case of
      // PARAMETERIZED-metakinded nodes (i.e. APPLYs); they could have a
      // buried ITE.

      // assume it's atomic if its kind can be atomic, check children
      // to see if that is actually true
      bool atomic = kind::kindCanBeAtomic(nv->getKind());
      if(atomic) {
        for(expr::NodeValue::nv_iterator i = nv->nv_begin();
            i != nv->nv_end();
            ++i) {
          if(!(atomic = isAtomic(*i))) {
            break;
          }
        }
      }

      setAttribute(nv, AtomicAttr(), atomic);
    }
  }
}

inline void NodeManager::poolRemove(expr::NodeValue* nv) {
  Assert(d_nodeValuePool.find(nv) != d_nodeValuePool.end(),
         "NodeValue is not in the pool!");

  d_nodeValuePool.erase(nv);// FIXME multithreading
}

}/* CVC4 namespace */

#define __CVC4__NODE_MANAGER_NEEDS_CONSTANT_MAP
#include "expr/metakind.h"
#undef __CVC4__NODE_MANAGER_NEEDS_CONSTANT_MAP

#include "expr/node_builder.h"

namespace CVC4 {

// general expression-builders

inline bool NodeManager::hasOperator(Kind k) {
  switch(kind::MetaKind mk = kind::metaKindOf(k)) {

  case kind::metakind::INVALID:
  case kind::metakind::VARIABLE:
    return false;

  case kind::metakind::OPERATOR:
  case kind::metakind::PARAMETERIZED:
    return true;

  case kind::metakind::CONSTANT:
    return false;

  default:
    Unhandled(mk);
  }
}

inline Node NodeManager::mkNode(Kind kind) {
  return NodeBuilder<>(this, kind);
}

inline Node NodeManager::mkNode(Kind kind, TNode child1) {
  return NodeBuilder<>(this, kind) << child1;
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2) {
  return NodeBuilder<>(this, kind) << child1 << child2;
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2,
                                TNode child3) {
  return NodeBuilder<>(this, kind) << child1 << child2 << child3;
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2,
                                TNode child3, TNode child4) {
  return NodeBuilder<>(this, kind) << child1 << child2 << child3 << child4;
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2,
                                TNode child3, TNode child4, TNode child5) {
  return NodeBuilder<>(this, kind) << child1 << child2 << child3 << child4
                                   << child5;
}

// N-ary version
template <bool ref_count>
inline Node NodeManager::mkNode(Kind kind,
                                const std::vector<NodeTemplate<ref_count> >&
                                children) {
  return NodeBuilder<>(this, kind).append(children);
}

inline Node NodeManager::mkVar(const std::string& name, Type* type) {
  Node n = mkVar(type);
  n.setAttribute(expr::VarNameAttr(), name);
  return n;
}

inline Node NodeManager::mkVar(Type* type) {
  Node n = Node(NodeBuilder<>(this, kind::VARIABLE));
  type->inc();// reference-count the type
  n.setAttribute(TypeAttr(), type);
  return n;
}

template <class T>
Node NodeManager::mkConst(const T& val) {
  // typedef typename kind::metakind::constantMap<T>::OwningTheory theory_t;

  NVStorage<1> nvStorage;
  expr::NodeValue& nvStack = reinterpret_cast<expr::NodeValue&>(nvStorage);

  nvStack.d_id = 0;
  nvStack.d_kind = kind::metakind::ConstantMap<T>::kind;
  nvStack.d_rc = 0;
  nvStack.d_nchildren = 1;
  nvStack.d_children[0] =
    const_cast<expr::NodeValue*>(reinterpret_cast<const expr::NodeValue*>(&val));
  expr::NodeValue* nv = poolLookup(&nvStack);

  if(nv != NULL) {
    return Node(nv);
  }

  nv = (expr::NodeValue*)
    std::malloc(sizeof(expr::NodeValue) + sizeof(T));
  if(nv == NULL) {
    throw std::bad_alloc();
  }

  nv->d_nchildren = 0;
  nv->d_kind = kind::metakind::ConstantMap<T>::kind;
  nv->d_id = expr::NodeValue::next_id++;// FIXME multithreading
  nv->d_rc = 0;

  //OwningTheory::mkConst(val);
  new (&nv->d_children) T(val);

  poolInsert(nv);
  Debug("gc") << "creating node value " << nv
              << " [" << nv->d_id << "]: " << *nv << "\n";

  return Node(nv);
}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */
