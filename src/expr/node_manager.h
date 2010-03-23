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
typedef ManagedAttribute<attr::Type, CVC4::Type*, attr::TypeCleanupFcn> TypeAttr;

}/* CVC4::expr namespace */

class NodeManager {
  static __thread NodeManager* s_current;

  template <class Builder> friend class CVC4::NodeBuilderBase;

  typedef __gnu_cxx::hash_set<expr::NodeValue*,
                              expr::NodeValueInternalHashFcn,
                              expr::NodeValue::NodeValueEq> NodeValuePool;
  typedef __gnu_cxx::hash_set<expr::NodeValue*,
                              expr::NodeValueIDHashFcn,
                              expr::NodeValue::NodeValueEq> ZombieSet;

  NodeValuePool d_nodeValuePool;

  expr::attr::AttributeManager d_attrManager;

  expr::NodeValue* poolLookup(expr::NodeValue* nv) const;
  void poolInsert(expr::NodeValue* nv);
  void poolRemove(expr::NodeValue* nv);

  friend class NodeManagerScope;
  friend class expr::NodeValue;

  bool isCurrentlyDeleting(const expr::NodeValue *nv) const{
    return d_underTheShotgun == nv;
  }

  expr::NodeValue* d_underTheShotgun;

  bool d_reclaiming;
  ZombieSet d_zombies;

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

  {
    poolInsert( &expr::NodeValue::s_null );
  }

  ~NodeManager();

  static NodeManager* currentNM() { return s_current; }

  // general expression-builders
  Node mkNode(Kind kind);
  Node mkNode(Kind kind, TNode child1);
  Node mkNode(Kind kind, TNode child1, TNode child2);
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3);
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3, TNode child4);
  Node mkNode(Kind kind, TNode child1, TNode child2, TNode child3, TNode child4, TNode child5);
  // N-ary version
  Node mkNode(Kind kind, const std::vector<Node>& children);

  // variables are special, because duplicates are permitted
  Node mkVar(Type* type, const std::string& name);
  Node mkVar(Type* type);
  Node mkVar();

  template <class AttrKind>
  inline typename AttrKind::value_type getAttribute(expr::NodeValue* nv,
                                                    const AttrKind&) const;

  // Note that there are two, distinct hasAttribute() declarations for
  // a reason (rather than using a pointer-valued argument with a
  // default value): they permit more optimized code in the underlying
  // hasAttribute() implementations.

  template <class AttrKind>
  inline bool hasAttribute(expr::NodeValue* nv,
                           const AttrKind&) const;

  template <class AttrKind>
  inline bool hasAttribute(expr::NodeValue* nv,
                           const AttrKind&,
                           typename AttrKind::value_type&) const;

  template <class AttrKind>
  inline void setAttribute(expr::NodeValue* nv,
                           const AttrKind&,
                           const typename AttrKind::value_type& value);

  template <class AttrKind>
  inline typename AttrKind::value_type getAttribute(TNode n,
                                                    const AttrKind&) const;

  // Note that there are two, distinct hasAttribute() declarations for
  // a reason (rather than using a pointer-valued argument with a
  // default value): they permit more optimized code in the underlying
  // hasAttribute() implementations.

  template <class AttrKind>
  inline bool hasAttribute(TNode n,
                           const AttrKind&) const;

  template <class AttrKind>
  inline bool hasAttribute(TNode n,
                           const AttrKind&,
                           typename AttrKind::value_type&) const;

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

  inline Type* getType(TNode n) const;
};

/**
 * Resource-acquisition-is-instantiation C++ idiom: create one of
 * these "scope" objects to temporarily change the thread-specific
 * notion of the "current" NodeManager for Node creation/deletion,
 * etc.  On destruction, the previous NodeManager pointer is restored.
 * Therefore such objects should only be created and destroyed in a
 * well-scoped manner (such as on the stack).
 *
 * This is especially useful on public-interface calls into the CVC4
 * library, where CVC4's notion of the "current" NodeManager should be
 * set to match the calling context.  See, for example, the
 * implementations of public calls in the ExprManager and SmtEngine
 * classes.
 *
 * You may create a NodeManagerScope with "new" and destroy it with
 * "delete", or place it as a data member of an object that is, but if
 * the scope of these new/delete pairs isn't properly maintained, the
 * incorrect "current" NodeManager pointer may be restored after a
 * delete.
 */
class NodeManagerScope {
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
 * A wrapper (essentially) for NodeManagerScope.  The current
 * "NodeManager" pointer is set to this Expr's underlying
 * ExpressionManager's NodeManager.  When the ExprManagerScope is
 * destroyed, the previous NodeManager is restored.
 *
 * This is especially useful on public-interface calls into the CVC4
 * library, where CVC4's notion of the "current" NodeManager should be
 * set to match the calling context.  See, for example, the
 * implementations of public calls in the Expr class.
 *
 * Without this, we'd need Expr to be a friend of ExprManager.
 */
class ExprManagerScope {
  NodeManagerScope d_nms;
public:
  inline ExprManagerScope(const Expr& e) :
    d_nms(e.getExprManager() == NULL
          ? NodeManager::currentNM()
          : e.getExprManager()->getNodeManager()) {
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
inline bool NodeManager::hasAttribute(expr::NodeValue* nv,
                                      const AttrKind&,
                                      typename AttrKind::value_type& ret) const {
  return d_attrManager.hasAttribute(nv, AttrKind(), ret);
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
inline bool NodeManager::hasAttribute(TNode n,
                                      const AttrKind&,
                                      typename AttrKind::value_type& ret) const {
  return d_attrManager.hasAttribute(n.d_nv, AttrKind(), ret);
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
