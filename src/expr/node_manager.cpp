/*********************                                                        */
/** node_manager.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Expression manager implementation.
 **/

#include "node_builder.h"
#include "node_manager.h"
#include "expr/node.h"
#include "util/output.h"

namespace CVC4 {

__thread NodeManager* NodeManager::s_current = 0;

NodeManager::NodeManager() {
  poolInsert(&NodeValue::s_null);
}

NodeValue* NodeManager::poolLookup(NodeValue* nv) const {
  NodeValueSet::const_iterator find = d_nodeValueSet.find(nv);
  if (find == d_nodeValueSet.end()) {
    return NULL;
  } else {
    return *find;
  }
}

void NodeManager::poolInsert(NodeValue* nv) {
  Assert(d_nodeValueSet.find(nv) == d_nodeValueSet.end(), "NodeValue already in"
         "the pool!");
  d_nodeValueSet.insert(nv);
}

// general expression-builders

Node NodeManager::mkNode(Kind kind) {
  return NodeBuilder<>(this, kind);
}

Node NodeManager::mkNode(Kind kind, const Node& child1) {
  return NodeBuilder<>(this, kind) << child1;
}

Node NodeManager::mkNode(Kind kind, const Node& child1, const Node& child2) {
  return NodeBuilder<>(this, kind) << child1 << child2;
}

Node NodeManager::mkNode(Kind kind, const Node& child1, const Node& child2, const Node& child3) {
  return NodeBuilder<>(this, kind) << child1 << child2 << child3;
}

Node NodeManager::mkNode(Kind kind, const Node& child1, const Node& child2, const Node& child3, const Node& child4) {
  return NodeBuilder<>(this, kind) << child1 << child2 << child3 << child4;
}

Node NodeManager::mkNode(Kind kind, const Node& child1, const Node& child2, const Node& child3, const Node& child4, const Node& child5) {
  return NodeBuilder<>(this, kind) << child1 << child2 << child3 << child4 << child5;
}

// N-ary version
Node NodeManager::mkNode(Kind kind, const std::vector<Node>& children) {
  return NodeBuilder<>(this, kind).append(children);
}

Node NodeManager::mkVar() {
  return NodeBuilder<>(this, VARIABLE);
}

}/* CVC4 namespace */
