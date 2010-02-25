/*********************                                                        */
/** expr_manager.cpp
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** [[ Add file-specific comments here ]]
 **/

/*
 * expr_manager.cpp
 *
 *  Created on: Dec 10, 2009
 *      Author: dejan
 */

#include "expr/node.h"
#include "expr/expr.h"
#include "expr/type.h"
#include "expr/node_manager.h"
#include "expr/expr_manager.h"

using namespace std;

namespace CVC4 {

ExprManager::ExprManager() :
  d_nodeManager(new NodeManager()) {
}

ExprManager::~ExprManager() {
  delete d_nodeManager;
}

const BooleanType* ExprManager::booleanType() const {
  NodeManagerScope nms(d_nodeManager);
  d_nodeManager->booleanType();
}

const KindType* ExprManager::kindType() const {
  NodeManagerScope nms(d_nodeManager);
  d_nodeManager->kindType();
}

Expr ExprManager::mkExpr(Kind kind) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind)));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode(),
                                          child2.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode(),
                                          child2.getNode(), child3.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3, const Expr& child4) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode(),
                                          child2.getNode(), child3.getNode(),
                                          child4.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3, const Expr& child4,
                         const Expr& child5) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode(),
                                          child2.getNode(), child3.getNode(),
                                          child5.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const vector<Expr>& children) {
  NodeManagerScope nms(d_nodeManager);

  vector<Node> nodes;
  vector<Expr>::const_iterator it = children.begin();
  vector<Expr>::const_iterator it_end = children.end();
  while(it != it_end) {
    nodes.push_back(it->getNode());
    ++it;
  }
  return Expr(this, new Node(d_nodeManager->mkNode(kind, nodes)));
}

/** Make a function type from domain to range. */
const FunctionType* 
ExprManager::mkFunctionType(const Type* domain, 
                            const Type* range) {
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkFunctionType(domain,range);
}

/** Make a function type with input types from argTypes. */
const FunctionType* 
ExprManager::mkFunctionType(const std::vector<const Type*>& argTypes, 
                            const Type* range) {
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkFunctionType(argTypes,range);
}

const Type* ExprManager::mkSort(const std::string& name) {
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkSort(name);
}

Expr ExprManager::mkVar(const Type* type, const std::string& name) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkVar(type, name)));
}

Expr ExprManager::mkVar(const Type* type) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkVar(type)));
}

NodeManager* ExprManager::getNodeManager() const {
  return d_nodeManager;
}

} // End namespace CVC4
