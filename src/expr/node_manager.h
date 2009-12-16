/*********************                                           -*- C++ -*-  */
/** expr_manager.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
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

public:
  static NodeManager* currentNM() { return s_current; }

  // general expression-builders
  Node mkExpr(Kind kind);
  Node mkExpr(Kind kind, const Node& child1);
  Node mkExpr(Kind kind, const Node& child1, const Node& child2);
  Node mkExpr(Kind kind, const Node& child1, const Node& child2, const Node& child3);
  Node mkExpr(Kind kind, const Node& child1, const Node& child2, const Node& child3, const Node& child4);
  Node mkExpr(Kind kind, const Node& child1, const Node& child2, const Node& child3, const Node& child4, const Node& child5);
  // N-ary version
  Node mkExpr(Kind kind, const std::vector<Node>& children);

  // variables are special, because duplicates are permitted
  Node mkVar();

  // TODO: these use the current NM (but must be renamed)
  /*
  static Node mkExpr(Kind kind)
  { currentNM()->mkExpr(kind); }
  static Node mkExpr(Kind kind, Node child1);
  { currentNM()->mkExpr(kind, child1); }
  static Node mkExpr(Kind kind, Node child1, Node child2);
  { currentNM()->mkExpr(kind, child1, child2); }
  static Node mkExpr(Kind kind, Node child1, Node child2, Node child3);
  { currentNM()->mkExpr(kind, child1, child2, child3); }
  static Node mkExpr(Kind kind, Node child1, Node child2, Node child3, Node child4);
  { currentNM()->mkExpr(kind, child1, child2, child3, child4); }
  static Node mkExpr(Kind kind, Node child1, Node child2, Node child3, Node child4, Node child5);
  { currentNM()->mkExpr(kind, child1, child2, child3, child4, child5); }
  */

  // do we want a varargs one?  perhaps not..
};

}/* CVC4 namespace */

#endif /* __CVC4__EXPR_MANAGER_H */
