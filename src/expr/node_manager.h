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

/* circular dependency; force node.h first */
#include "expr/attribute.h"
#include "expr/node.h"

#ifndef __CVC4__NODE_MANAGER_H
#define __CVC4__NODE_MANAGER_H

#include <vector>
#include <string>
#include <ext/hash_set>

#include "expr/kind.h"

namespace __gnu_cxx {
  template<>
  struct hash<CVC4::NodeValue*> {
    size_t operator()(const CVC4::NodeValue* nv) const {
      return (size_t)nv->hash();
    }
  };
}/* __gnu_cxx namespace */


namespace CVC4 {

class Type;

namespace expr {
namespace attr {

struct VarName {};
struct Type {};

}/* CVC4::expr::attr namespace */

typedef Attribute<attr::VarName, std::string> VarNameAttr;
typedef Attribute<attr::Type, const CVC4::Type*> TypeAttr;

}/* CVC4::expr namespace */

class NodeManager {
  static __thread NodeManager* s_current;

  template <unsigned> friend class CVC4::NodeBuilder;

  typedef __gnu_cxx::hash_set<NodeValue*, __gnu_cxx::hash<NodeValue*>, NodeValue::NodeValueEq> NodeValueSet;
  NodeValueSet d_nodeValueSet;

  expr::attr::AttributeManager d_attrManager;

  NodeValue* poolLookup(NodeValue* nv) const;
  void poolInsert(NodeValue* nv);

  friend class NodeManagerScope;

public:

  NodeManager() {
    poolInsert( &NodeValue::s_null );
  }

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
  Node mkVar(const Type* type, const std::string& name);
  Node mkVar(const Type* type);
  Node mkVar();

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

  inline const Type* getType(TNode n);
};

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

template <class AttrKind>
inline typename AttrKind::value_type NodeManager::getAttribute(TNode n,
                                                               const AttrKind&) const {
  return d_attrManager.getAttribute(n, AttrKind());
}

template <class AttrKind>
inline bool NodeManager::hasAttribute(TNode n,
                                      const AttrKind&) const {
  return d_attrManager.hasAttribute(n, AttrKind());
}

template <class AttrKind>
inline bool NodeManager::hasAttribute(TNode n,
                                      const AttrKind&,
                                      typename AttrKind::value_type& ret) const {
  return d_attrManager.hasAttribute(n, AttrKind(), ret);
}

template <class AttrKind>
inline void NodeManager::setAttribute(TNode n,
                                      const AttrKind&,
                                      const typename AttrKind::value_type& value) {
  d_attrManager.setAttribute(n, AttrKind(), value);
}

inline const Type* NodeManager::getType(TNode n) {
  return getAttribute(n,CVC4::expr::TypeAttr());
}

inline void NodeManager::poolInsert(NodeValue* nv) {
  Assert(d_nodeValueSet.find(nv) == d_nodeValueSet.end(), "NodeValue already in"
         "the pool!");
  d_nodeValueSet.insert(nv);
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

inline Node NodeManager::mkVar(const Type* type, const std::string& name) {
  Node n = mkVar(type);
  n.setAttribute(expr::VarNameAttr(), name);
  return n;
}

inline Node NodeManager::mkVar(const Type* type) {
  Node n = NodeBuilder<>(this, kind::VARIABLE);
  n.setAttribute(expr::TypeAttr(), type);
  return n;
}

inline Node NodeManager::mkVar() {
  return NodeBuilder<>(this, kind::VARIABLE);
}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */
