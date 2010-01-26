/*********************                                           -*- C++ -*-  */
/** node_manager.cpp
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): dejan
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
#include "util/output.h"

namespace CVC4 {

__thread NodeManager* NodeManager::s_current = 0;

Node NodeManager::lookup(uint64_t hash, NodeValue* ev) {
  Assert(this != NULL, "Whoops, we have a bad expression manager!");
  Assert(ev != NULL, "lookup() expects a non-NULL NodeValue!");

  hash_t::iterator i = d_hash.find(hash);
  if(i == d_hash.end()) {
    // insert
    std::vector<Node> v;
    Node e(ev);
    v.push_back(e);
    d_hash.insert(std::make_pair(hash, v));
    return e;
  } else {
    for(std::vector<Node>::iterator j = i->second.begin(); j != i->second.end(); ++j) {
      if(ev->getKind() != j->getKind()) {
        continue;
      }

      if(ev->numChildren() != j->numChildren()) {
        continue;
      }

      NodeValue::const_ev_iterator c1 = ev->ev_begin();
      NodeValue::ev_iterator c2 = j->d_ev->ev_begin();
      for(; c1 != ev->ev_end() && c2 != j->d_ev->ev_end(); ++c1, ++c2) {
        if(*c1 != *c2) {
          break;
        }
      }

      if(c1 != ev->ev_end() || c2 != j->d_ev->ev_end()) {
        continue;
      }

      return *j;
    }

    // didn't find it, insert
    std::vector<Node> v;
    Node e(ev);
    v.push_back(e);
    d_hash.insert(std::make_pair(hash, v));
    return e;
  }
}

NodeValue* NodeManager::lookupNoInsert(uint64_t hash, NodeValue* ev) {
  Assert(this != NULL, "Whoops, we have a bad expression manager!");
  Assert(ev != NULL, "lookupNoInsert() expects a non-NULL NodeValue!");

  hash_t::iterator i = d_hash.find(hash);
  if(i == d_hash.end()) {
    return NULL;
  } else {
    for(std::vector<Node>::iterator j = i->second.begin(); j != i->second.end(); ++j) {
      if(ev->getKind() != j->getKind()) {
        continue;
      }

      if(ev->numChildren() != j->numChildren()) {
        continue;
      }

      NodeValue::const_ev_iterator c1 = ev->ev_begin();
      NodeValue::ev_iterator c2 = j->d_ev->ev_begin();
      for(; c1 != ev->ev_end() && c2 != j->d_ev->ev_end(); ++c1, ++c2) {
        Debug("expr") << "comparing " << c1 << " and " << c2 << std::endl;
        if(*c1 != *c2) {
          break;
        }
      }

      if(c1 != ev->ev_end() || c2 != j->d_ev->ev_end()) {
        continue;
      }

      return j->d_ev;
    }

    // didn't find it, don't insert
    return 0;
  }
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
