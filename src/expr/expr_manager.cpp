/*
 * expr_manager.cpp
 *
 *  Created on: Dec 10, 2009
 *      Author: dejan
 */

#include "expr/node.h"
#include "expr/expr.h"
#include "expr/node_manager.h"
#include "expr/expr_manager.h"

using namespace std;

namespace CVC4 {

ExprManager::ExprManager()
: d_nm(new NodeManager()) {
}

ExprManager::~ExprManager() {
  delete d_nm;
}

Expr ExprManager::mkExpr(Kind kind) {
  return Expr(this, new Node(d_nm->mkNode(kind)));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1) {
  return Expr(this, new Node(d_nm->mkNode(kind, child1.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2) {
  return Expr(this, new Node(d_nm->mkNode(kind, child1.getNode(),
                                          child2.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3) {
  return Expr(this, new Node(d_nm->mkNode(kind, child1.getNode(),
                                          child2.getNode(), child3.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3, const Expr& child4) {
  return Expr(this, new Node(d_nm->mkNode(kind, child1.getNode(),
                                          child2.getNode(), child3.getNode(),
                                          child4.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3, const Expr& child4,
                         const Expr& child5) {
  return Expr(this, new Node(d_nm->mkNode(kind, child1.getNode(),
                                          child2.getNode(), child3.getNode(),
                                          child5.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const vector<Expr>& children) {
  vector<Node> nodes;
  vector<Expr>::const_iterator it = children.begin();
  vector<Expr>::const_iterator it_end = children.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  return Expr(this, new Node(d_nm->mkNode(kind, nodes)));
}

Expr ExprManager::mkVar() {
  return Expr(this, new Node(d_nm->mkVar()));
}

NodeManager* ExprManager::getNodeManager() const {
  return d_nm;
}

} // End namespace CVC4
