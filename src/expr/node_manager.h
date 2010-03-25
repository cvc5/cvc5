/*********************                                                        */
/** node_manager.h
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A manager for Nodes.
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
#include "expr/expr.h"
#include "expr/node_value.h"
#include "context/context.h"
#include "expr/type.h"

namespace CVC4 {

class Type;

namespace expr {
namespace attr {

struct VarName {};
struct Type {};

}/* CVC4::expr::attr namespace */

typedef Attribute<attr::VarName, std::string> VarNameAttr;
typedef ManagedAttribute<attr::Type, CVC4::Type*, attr::TypeCleanupStrategy> TypeAttr;

}/* CVC4::expr namespace */

class NodeManager {
  template <class Builder> friend class CVC4::NodeBuilderBase;
  friend class NodeManagerScope;
  friend class expr::NodeValue;

  typedef __gnu_cxx::hash_set<expr::NodeValue*,
                              expr::NodeValueInternalHashFunction,
                              expr::NodeValue::NodeValueEq> NodeValuePool;
  typedef __gnu_cxx::hash_set<expr::NodeValue*,
                              expr::NodeValueIDHashFunction,
                              expr::NodeValue::NodeValueEq> ZombieSet;

  static __thread NodeManager* s_current;

  NodeValuePool d_nodeValuePool;

  expr::attr::AttributeManager d_attrManager;
  expr::NodeValue* d_underTheShotgun;

  bool d_reclaiming;
  ZombieSet d_zombies;

  expr::NodeValue* poolLookup(expr::NodeValue* nv) const;
  void poolInsert(expr::NodeValue* nv);
  void poolRemove(expr::NodeValue* nv);

  bool isCurrentlyDeleting(const expr::NodeValue *nv) const{
    return d_underTheShotgun == nv;
  }

  /**
   * Register a NodeValue as a zombie.
   */
  inline void gc(expr::NodeValue* nv) {
    Assert(nv->d_rc == 0);
    if(d_reclaiming) {// FIXME multithreading
      // currently reclaiming zombies; just push onto the list
      Debug("gc") << "zombifying node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString()
                  << " [CURRENTLY-RECLAIMING]\n";
      d_zombies.insert(nv);// FIXME multithreading
    } else {
      Debug("gc") << "zombifying node value " << nv
                  << " [" << nv->d_id << "]: " << nv->toString() << "\n";
      d_zombies.insert(nv);// FIXME multithreading

      // for now, collect eagerly.  can add heuristic here later..
      reclaimZombies();
    }
  }

  /**
   * Reclaim all zombies.
   */
  void reclaimZombies();

public:

  NodeManager(context::Context* ctxt) :
    d_attrManager(ctxt),
    d_underTheShotgun(NULL),
    d_reclaiming(false)

  { // static initialization
    poolInsert( &expr::NodeValue::s_null );
  }

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
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3, TNode child4);

  /** Create a node with five children. */
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3, TNode child4, TNode child5);

  /** Create a node with an arbitrary number of children. */
  Node mkNode(Kind kind, const std::vector<Node>& children);

  // NOTE: variables are special, because duplicates are permitted

  /** Create a variable with the given type and name. */
  Node mkVar(Type* type, const std::string& name);

  /** Create a variable with the given type. */
  Node mkVar(Type* type);

  /** Create a variable of unknown type (?). */
  Node mkVar();

  /** Retrieve an attribute for a node.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to retrieve.
   * @returns the attribute, if set, or a default-constructed
   * <code>AttrKind::value_type</code> if not.
   */
  template <class AttrKind>
  inline typename AttrKind::value_type getAttribute(expr::NodeValue* nv,
                                                    const AttrKind& attr) const;

  /* NOTE: there are two, distinct hasAttribute() declarations for
   a reason (rather than using a pointer-valued argument with a
   default value): they permit more optimized code in the underlying
   hasAttribute() implementations. */

  /** Check whether an attribute is set for a node.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to check
   * @returns <code>true</code> iff <code>attr</code> is set for <code>nv</code>.
   */
  template <class AttrKind>
  inline bool hasAttribute(expr::NodeValue* nv,
                           const AttrKind& attr) const;

  /** Check whether an attribute is set for a node.
   *
   * @param nv the node value
   * @param attr an instance of the attribute kind to check
   * @param value a reference to an object of the attribute's value type.
   * <code>value</code> will be set to the value of the attribute, if it is
   * set for <code>nv</code>; otherwise, it will be set to the default value of
   * the attribute.
   * @returns <code>true</code> iff <code>attr</code> is set for <code>nv</code>.
   */
  template <class AttrKind>
  inline bool getAttribute(expr::NodeValue* nv,
                           const AttrKind& attr,
                           typename AttrKind::value_type& value) const;

  /** Set an attribute for a node.
    *
    * @param nv the node value
    * @param attr an instance of the attribute kind to set
    * @param value the value of <code>attr</code> for <code>nv</code>
    */
  template <class AttrKind>
  inline void setAttribute(expr::NodeValue* nv,
                           const AttrKind&,
                           const typename AttrKind::value_type& value);

  /** Retrieve an attribute for a TNode.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to retrieve.
   * @returns the attribute, if set, or a default-constructed
   * <code>AttrKind::value_type</code> if not.
   */
  template <class AttrKind>
  inline typename AttrKind::value_type getAttribute(TNode n,
                                                    const AttrKind&) const;

  /* NOTE: there are two, distinct hasAttribute() declarations for
   a reason (rather than using a pointer-valued argument with a
   default value): they permit more optimized code in the underlying
   hasAttribute() implementations. */

  /** Check whether an attribute is set for a TNode.
   *
   * @param n the node
   * @param attr an instance of the attribute kind to check
   * @returns <code>true</code> iff <code>attr</code> is set for <code>n</code>.
   */
  template <class AttrKind>
  inline bool hasAttribute(TNode n,
                           const AttrKind& attr) const;

  /** Check whether an attribute is set for a TNode.
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

  /** Set an attribute for a TNode.
    *
    * @param n the node
    * @param attr an instance of the attribute kind to set
    * @param value the value of <code>attr</code> for <code>n</code>
    */
  template <class AttrKind>
  inline void setAttribute(TNode n,
                           const AttrKind&,
                           const typename AttrKind::value_type& value);

  /** Get the type for booleans. */
  inline BooleanType* booleanType() const {
    return BooleanType::getInstance();
  }

  /** Get the type for sorts. */
  inline KindType* kindType() const {
    return KindType::getInstance();
  }

  /** Make a function type from domain to range. */
  inline FunctionType* mkFunctionType(Type* domain, Type* range) const;

  /** Make a function type with input types from argTypes. */
  inline FunctionType* mkFunctionType(const std::vector<Type*>& argTypes,
                                      Type* range) const;

  /** Make a new sort with the given name. */
  inline Type* mkSort(const std::string& name) const;

  /** Get the type for the given node.
   *
   * TODO: Does this call compute the type if it's not already available?
   */
  inline Type* getType(TNode n) const;
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
    Debug("current") << "node manager scope: " << NodeManager::s_current << "\n";
  }

  ~NodeManagerScope() {
    NodeManager::s_current = d_oldNodeManager;
    Debug("current") << "node manager scope: returning to " << NodeManager::s_current << "\n";
  }
};

/**
 * Creates
 * a <code>NodeManagerScope</code> with the underlying <code>NodeManager</code>
 * of a given <code>Expr</code> or <code>ExprManager</code>.
 * The <code>NodeManagerScope</code> is destroyed when the <code>ExprManagerScope</code>
 * is destroyed. See <code>NodeManagerScope</code> for more information.
 */
// NOTE: Without this, we'd need Expr to be a friend of ExprManager.
// [chris 3/25/2010] Why?
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
inline typename AttrKind::value_type NodeManager::getAttribute(expr::NodeValue* nv,
                                                               const AttrKind&) const {
  return d_attrManager.getAttribute(nv, AttrKind());
}

template <class AttrKind>
inline bool NodeManager::hasAttribute(expr::NodeValue* nv,
                                      const AttrKind&) const {
  return d_attrManager.hasAttribute(nv, AttrKind());
}

template <class AttrKind>
inline bool NodeManager::getAttribute(expr::NodeValue* nv,
                                      const AttrKind&,
                                      typename AttrKind::value_type& ret) const {
  return d_attrManager.getAttribute(nv, AttrKind(), ret);
}

template <class AttrKind>
inline void NodeManager::setAttribute(expr::NodeValue* nv,
                                      const AttrKind&,
                                      const typename AttrKind::value_type& value) {
  d_attrManager.setAttribute(nv, AttrKind(), value);
}

template <class AttrKind>
inline typename AttrKind::value_type NodeManager::getAttribute(TNode n,
                                                               const AttrKind&) const {
  return d_attrManager.getAttribute(n.d_nv, AttrKind());
}

template <class AttrKind>
inline bool NodeManager::hasAttribute(TNode n,
                                      const AttrKind&) const {
  return d_attrManager.hasAttribute(n.d_nv, AttrKind());
}

template <class AttrKind>
inline bool NodeManager::getAttribute(TNode n,
                                      const AttrKind&,
                                      typename AttrKind::value_type& ret) const {
  return d_attrManager.getAttribute(n.d_nv, AttrKind(), ret);
}

template <class AttrKind>
inline void NodeManager::setAttribute(TNode n,
                                      const AttrKind&,
                                      const typename AttrKind::value_type& value) {
  d_attrManager.setAttribute(n.d_nv, AttrKind(), value);
}

/** Make a function type from domain to range.
 * TODO: Function types should be unique for this manager. */
FunctionType* NodeManager::mkFunctionType(Type* domain,
                                          Type* range) const {
  std::vector<Type*> argTypes;
  argTypes.push_back(domain);
  return new FunctionType(argTypes, range);
}

/** Make a function type with input types from argTypes.
 * TODO: Function types should be unique for this manager. */
FunctionType* NodeManager::mkFunctionType(const std::vector<Type*>& argTypes,
                                          Type* range) const {
  Assert( argTypes.size() > 0 );
  return new FunctionType(argTypes, range);
}

Type* NodeManager::mkSort(const std::string& name) const {
  return new SortType(name);
}

inline Type* NodeManager::getType(TNode n) const {
  return getAttribute(n, CVC4::expr::TypeAttr());
}

inline void NodeManager::poolInsert(expr::NodeValue* nv) {
  Assert(d_nodeValuePool.find(nv) == d_nodeValuePool.end(),
         "NodeValue already in the pool!");
  d_nodeValuePool.insert(nv);// FIXME multithreading
}

inline void NodeManager::poolRemove(expr::NodeValue* nv) {
  Assert(d_nodeValuePool.find(nv) != d_nodeValuePool.end(),
         "NodeValue is not in the pool!");
  d_nodeValuePool.erase(nv);// FIXME multithreading
}

}/* CVC4 namespace */

#include "expr/node_builder.h"

namespace CVC4 {

// general expression-builders

inline Node NodeManager::mkNode(Kind kind) {
  return NodeBuilder<>(this, kind);
}

inline Node NodeManager::mkNode(Kind kind, TNode child1) {
  return NodeBuilder<>(this, kind) << child1;
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2) {
  return NodeBuilder<>(this, kind) << child1 << child2;
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2, TNode child3) {
  return NodeBuilder<>(this, kind) << child1 << child2 << child3;
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2, TNode child3, TNode child4) {
  return NodeBuilder<>(this, kind) << child1 << child2 << child3 << child4;
}

inline Node NodeManager::mkNode(Kind kind, TNode child1, TNode child2, TNode child3, TNode child4, TNode child5) {
  return NodeBuilder<>(this, kind) << child1 << child2 << child3 << child4 << child5;
}

// N-ary version
inline Node NodeManager::mkNode(Kind kind, const std::vector<Node>& children) {
  return NodeBuilder<>(this, kind).append(children);
}

inline Node NodeManager::mkVar(Type* type, const std::string& name) {
  Node n = mkVar(type);
  n.setAttribute(expr::VarNameAttr(), name);
  return n;
}

inline Node NodeManager::mkVar(Type* type) {
  Node n = mkVar();
  type->inc();// reference-count the type
  n.setAttribute(expr::TypeAttr(), type);
  return n;
}

inline Node NodeManager::mkVar() {
  // TODO: rewrite to not use NodeBuilder
  return NodeBuilder<>(this, kind::VARIABLE);
}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */
