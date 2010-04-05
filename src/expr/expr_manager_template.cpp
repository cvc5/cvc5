/*********************                                                        */
/** expr_manager_template.cpp
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
 ** Public-facing expression manager interface, implementation.
 **/

#include "expr/node.h"
#include "expr/expr.h"
#include "expr/kind.h"
#include "expr/metakind.h"
#include "expr/type.h"
#include "expr/node_manager.h"
#include "expr/expr_manager.h"
#include "context/context.h"

${includes}

// This is a hack, but an important one: if there's an error, the
// compiler directs the user to the template file instead of the
// generated one.  We don't want the user to modify the generated one,
// since it'll get overwritten on a later build.
#line 32 "${template}"

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
  const unsigned n = 0;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind)));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1) {
  const unsigned n = 1;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2) {
  const unsigned n = 2;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode(),
                                          child2.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3) {
  const unsigned n = 3;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode(),
                                          child2.getNode(), child3.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3, const Expr& child4) {
  const unsigned n = 4;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode(),
                                          child2.getNode(), child3.getNode(),
                                          child4.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2,
                         const Expr& child3, const Expr& child4,
                         const Expr& child5) {
  const unsigned n = 5;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkNode(kind, child1.getNode(),
                                          child2.getNode(), child3.getNode(),
                                          child5.getNode())));
}

Expr ExprManager::mkExpr(Kind kind, const vector<Expr>& children) {
  const unsigned n = children.size();
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);

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

FunctionType* ExprManager::mkFunctionType(const std::vector<Type*>& sorts) {
  Assert( sorts.size() >= 2 );
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkFunctionType(sorts);
}

FunctionType* ExprManager::mkPredicateType(const std::vector<Type*>& sorts) {
  Assert( sorts.size() >= 1 );
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkPredicateType(sorts);
}

Type* ExprManager::mkSort(const std::string& name) {
  NodeManagerScope nms(d_nodeManager);
  return d_nodeManager->mkSort(name);
}

Expr ExprManager::mkVar(const std::string& name, Type* type) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkVar(name, type)));
}

Expr ExprManager::mkVar(Type* type) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, new Node(d_nodeManager->mkVar(type)));
}

unsigned ExprManager::minArity(Kind kind) {
  return metakind::getLowerBoundForKind(kind);
}

unsigned ExprManager::maxArity(Kind kind) {
  return metakind::getUpperBoundForKind(kind);
}

NodeManager* ExprManager::getNodeManager() const {
  return d_nodeManager;
}

Context* ExprManager::getContext() const {
  return d_ctxt;
}

${mkConst_implementations}

}/* CVC4 namespace */
