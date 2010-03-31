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

#include "context/context.h"
#include "expr/expr.h"
#include "expr/expr_manager.h"
#include "expr/kind.h"
#include "expr/node.h"
#include "expr/node_manager.h"
#include "expr/type.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4::kind;

namespace CVC4 {

ExprManager::ExprManager() :
  d_ctxt(new Context),
  d_nodeManager(new NodeManager(d_ctxt)) {
}

ExprManager::~ExprManager() {
  delete d_nodeManager;
  delete d_ctxt;
}

BooleanType* ExprManager::booleanType() const {
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->booleanType();
}

KindType* ExprManager::kindType() const {
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->kindType();
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
FunctionType* ExprManager::mkFunctionType(Type* domain,
                                          Type* range) {
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkFunctionType(domain, range);
}

/** Make a function type with input types from argTypes. */
FunctionType* ExprManager::mkFunctionType(const std::vector<Type*>& argTypes,
                                          Type* range) {
  Assert( argTypes.size() >= 1 );
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkFunctionType(argTypes, range);
}

FunctionType*
ExprManager::mkFunctionType(const std::vector<Type*>& sorts) {
  Assert( sorts.size() >= 2 );
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkFunctionType(sorts);
}

FunctionType*
ExprManager::mkPredicateType(const std::vector<Type*>& sorts) {
  Assert( sorts.size() >= 1 );
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkPredicateType(sorts);
}

Type* ExprManager::mkSort(const std::string& name) {
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkSort(name);
}

Expr ExprManager::mkVar(Type* type, const std::string& name) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkVar(type, name)));
}

Expr ExprManager::mkVar(Type* type) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkVar(type)));
}

unsigned int ExprManager::minArity(Kind kind) {
  switch(kind) {
  case FALSE:
  case SKOLEM:
  case TRUE:
  case VARIABLE:
    return 0;

  case AND:
  case NOT:
  case OR:
    return 1;

  case APPLY_UF:
  case DISTINCT:
  case EQUAL:
  case IFF:
  case IMPLIES:
  case PLUS:
  case XOR:
    return 2;

  case ITE:
    return 3;

  default:
    Unhandled(kind);
  }
}

unsigned int ExprManager::maxArity(Kind kind) {
  switch(kind) {
  case FALSE:
  case SKOLEM:
  case TRUE:
  case VARIABLE:
    return 0;

  case NOT:
    return 1;

  case EQUAL:
  case IFF:
  case IMPLIES:
  case XOR:
    return 2;

  case ITE:
    return 3;

  case AND:
  case APPLY_UF:
  case DISTINCT:
  case PLUS:
  case OR:
    return UINT_MAX;

  default:
    Unhandled(kind);
  }
}


NodeManager* ExprManager::getNodeManager() const {
  return d_nodeManager;
}

Context* ExprManager::getContext() const {
  return d_ctxt;
}

}/* CVC4 namespace */
