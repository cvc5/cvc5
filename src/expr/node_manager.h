/*********************                                           -*- C++ -*-  */
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
#include <map>

#include "node.h"
#include "kind.h"

namespace CVC4 {

class NodeManager {
  static __thread NodeManager* s_current;

  template <unsigned> friend class CVC4::NodeBuilder;

  typedef std::map<uint64_t, std::vector<Node> > hash_t;
  hash_t d_hash;

  Node lookup(uint64_t hash, const Node& e) { return lookup(hash, e.d_ev); }
  Node lookup(uint64_t hash, NodeValue* e);
  NodeValue* lookupNoInsert(uint64_t hash, NodeValue* e);

  friend class NodeManagerScope;

public:
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
  Node mkVar();
};


class NodeManagerScope {
  NodeManager *d_oldNodeManager;

public:
  NodeManagerScope(NodeManager* nm) : d_oldNodeManager(NodeManager::s_current) {
    NodeManager::s_current = nm;
  }
  ~NodeManagerScope() {
    NodeManager::s_current = d_oldNodeManager;
  }
};

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */
