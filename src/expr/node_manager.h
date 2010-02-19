/*********************                                                        */
/** node_manager.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): taking, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A manager for Nodes.
 **/

#ifndef __CVC4__NODE_MANAGER_H
#define __CVC4__NODE_MANAGER_H

#include <vector>
#include <string>
#include <ext/hash_set>

#include "expr/node.h"
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

class NodeManager {
  static __thread NodeManager* s_current;

  template <unsigned> friend class CVC4::NodeBuilder;

  typedef __gnu_cxx::hash_set<NodeValue*, __gnu_cxx::hash<NodeValue*>, NodeValue::NodeValueEq> NodeValueSet;
  NodeValueSet d_nodeValueSet;

  expr::AttributeManager d_am;

  NodeValue* poolLookup(NodeValue* nv) const;
  void poolInsert(NodeValue* nv);

  friend class NodeManagerScope;

public:

  NodeManager() : d_am(this) {
    poolInsert( &NodeValue::s_null );
  }

  static NodeManager* currentNM() { return s_current; }

  // general expression-builders
  Node mkNode(Kind kind);
  Node mkNode(Kind kind, const Node& child1);
  Node mkNode(Kind kind, const Node& child1, const Node& child2);
  Node mkNode(Kind kind, const Node& child1, const Node& child2, const Node& child3);
  Node mkNode(Kind kind, const Node& child1, const Node& child2, const Node& child3, const Node& child4);
  Node mkNode(Kind kind, const Node& child1, const Node& child2, const Node& child3, const Node& child4, const Node& child5);
  // N-ary version
  Node mkNode(Kind kind, const std::vector<Node>& children);

  // variables are special, because duplicates are permitted
  Node mkVar(const Type* type, std::string name);
  Node mkVar(const Type* type);
  Node mkVar();

  template <class AttrKind>
  inline typename AttrKind::value_type getAttribute(const Node& n,
                                                    const AttrKind&);

  template <class AttrKind>
  inline bool hasAttribute(const Node& n,
                           const AttrKind&,
                           typename AttrKind::value_type* = NULL);

  template <class AttrKind>
  inline void setAttribute(const Node& n,
                           const AttrKind&,
                           const typename AttrKind::value_type& value);
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
inline typename AttrKind::value_type NodeManager::getAttribute(const Node& n,
                                                               const AttrKind&) {
  return d_am.getAttribute(n, AttrKind());
}

template <class AttrKind>
inline bool NodeManager::hasAttribute(const Node& n,
                                      const AttrKind&,
                                      typename AttrKind::value_type* ret) {
  return d_am.hasAttribute(n, AttrKind(), ret);
}

template <class AttrKind>
inline void NodeManager::setAttribute(const Node& n,
                                      const AttrKind&,
                                      const typename AttrKind::value_type& value) {
  d_am.setAttribute(n, AttrKind(), value);
}

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */
