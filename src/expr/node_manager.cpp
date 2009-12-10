/*********************                                           -*- C++ -*-  */
/** expr_manager.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
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

namespace CVC4 {

__thread NodeManager* NodeManager::s_current = 0;

Node NodeManager::lookup(uint64_t hash, const Node& e) {
  Assert(this != NULL, "Woops, we have a bad expression manager!");
  hash_t::iterator i = d_hash.find(hash);
  if(i == d_hash.end()) {
    // insert
    std::vector<Node> v;
    v.push_back(e);
    d_hash.insert(std::make_pair(hash, v));
    return e;
  } else {
    for(std::vector<Node>::iterator j = i->second.begin(); j != i->second.end(); ++j) {
      if(e.getKind() != j->getKind())
        continue;

      if(e.numChildren() != j->numChildren())
        continue;

      Node::const_iterator c1 = e.begin();
      Node::iterator c2 = j->begin();
      for(; c1 != e.end() && c2 != j->end(); ++c1, ++c2) {
        if(c1->d_ev != c2->d_ev)
          break;
      }

      if(c1 != e.end() || c2 != j->end())
        continue;

      return *j;
    }
    // didn't find it, insert
    std::vector<Node> v;
    v.push_back(e);
    d_hash.insert(std::make_pair(hash, v));
    return e;
  }
}

// general expression-builders

Node NodeManager::mkExpr(Kind kind) {
  return NodeBuilder(this, kind);
}

Node NodeManager::mkExpr(Kind kind, const Node& child1) {
  return NodeBuilder(this, kind) << child1;
}

Node NodeManager::mkExpr(Kind kind, const Node& child1, const Node& child2) {
  return NodeBuilder(this, kind) << child1 << child2;
}

Node NodeManager::mkExpr(Kind kind, const Node& child1, const Node& child2, const Node& child3) {
  return NodeBuilder(this, kind) << child1 << child2 << child3;
}

Node NodeManager::mkExpr(Kind kind, const Node& child1, const Node& child2, const Node& child3, const Node& child4) {
  return NodeBuilder(this, kind) << child1 << child2 << child3 << child4;
}

Node NodeManager::mkExpr(Kind kind, const Node& child1, const Node& child2, const Node& child3, const Node& child4, const Node& child5) {
  return NodeBuilder(this, kind) << child1 << child2 << child3 << child4 << child5;
}

// N-ary version
Node NodeManager::mkExpr(Kind kind, std::vector<Node> children) {
  return NodeBuilder(this, kind).append(children);
}

Node NodeManager::mkVar() {
  return NodeBuilder(this, VARIABLE);
}

}/* CVC4 namespace */
