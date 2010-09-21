/*********************                                                        */
/*! \file expr_manager_template.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: cconway, mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Public-facing expression manager interface, implementation.
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
#line 35 "${template}"

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

BooleanType ExprManager::booleanType() const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->booleanType()));
}

KindType ExprManager::kindType() const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->kindType()));
}

RealType ExprManager::realType() const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->realType()));
}

IntegerType ExprManager::integerType() const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->integerType()));
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1) {
  const unsigned n = 1;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    return Expr(this, d_nodeManager->mkNodePtr(kind, child1.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(Expr(this, new Node(e.getNode())), e.getMessage());
  }
}

Expr ExprManager::mkExpr(Kind kind, const Expr& child1, const Expr& child2) {
  const unsigned n = 2;
  CheckArgument(n >= minArity(kind) && n <= maxArity(kind), kind,
                "Exprs with kind %s must have at least %u children and "
                "at most %u children (the one under construction has %u)",
                kind::kindToString(kind).c_str(),
                minArity(kind), maxArity(kind), n);
  NodeManagerScope nms(d_nodeManager);
  try {
    return Expr(this, d_nodeManager->mkNodePtr(kind, 
                                               child1.getNode(),
                                               child2.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(Expr(this, new Node(e.getNode())), 
                                e.getMessage());
  }
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
  try {
    return Expr(this, d_nodeManager->mkNodePtr(kind, 
                                               child1.getNode(), 
                                               child2.getNode(), 
                                               child3.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(Expr(this, new Node(e.getNode())), 
                                e.getMessage());
  }
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
  try {
    return Expr(this, d_nodeManager->mkNodePtr(kind, 
                                               child1.getNode(),
                                               child2.getNode(), 
                                               child3.getNode(),
                                               child4.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(Expr(this, new Node(e.getNode())), 
                                e.getMessage());
  }
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
  try {
    return Expr(this, d_nodeManager->mkNodePtr(kind, 
                                               child1.getNode(),
                                               child2.getNode(), 
                                               child3.getNode(),
                                               child4.getNode(),
                                               child5.getNode()));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(Expr(this, new Node(e.getNode())), 
                                e.getMessage());
  }
}

Expr ExprManager::mkExpr(Kind kind, const std::vector<Expr>& children) {
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
  try {
    return Expr(this, d_nodeManager->mkNodePtr(kind, nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(Expr(this, new Node(e.getNode())), 
                                e.getMessage());
  }
}

Expr ExprManager::mkExpr(Expr opExpr, const std::vector<Expr>& children) {
  const unsigned n = children.size();
  Kind kind = kind::operatorKindToKind(opExpr.getKind());
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
  try {
    return Expr(this,d_nodeManager->mkNodePtr(opExpr.getNode(), nodes));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(Expr(this, new Node(e.getNode())), e.getMessage());
  }
}

/** Make a function type from domain to range. */
FunctionType ExprManager::mkFunctionType(const Type& domain, const Type& range) {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(*domain.d_typeNode, *range.d_typeNode)));
}

/** Make a function type with input types from argTypes. */
FunctionType ExprManager::mkFunctionType(const std::vector<Type>& argTypes, const Type& range) {
  Assert( argTypes.size() >= 1 );
  NodeManagerScope nms(d_nodeManager);
  std::vector<TypeNode> argTypeNodes;
  for (unsigned i = 0, i_end = argTypes.size(); i < i_end; ++ i) {
    argTypeNodes.push_back(*argTypes[i].d_typeNode);
  }
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(argTypeNodes, *range.d_typeNode)));
}

FunctionType ExprManager::mkFunctionType(const std::vector<Type>& sorts) {
  Assert( sorts.size() >= 2 );
  NodeManagerScope nms(d_nodeManager);
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0, i_end = sorts.size(); i < i_end; ++ i) {
     sortNodes.push_back(*sorts[i].d_typeNode);
  }
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkFunctionType(sortNodes)));
}

FunctionType ExprManager::mkPredicateType(const std::vector<Type>& sorts) {
  Assert( sorts.size() >= 1 );
  NodeManagerScope nms(d_nodeManager);
  std::vector<TypeNode> sortNodes;
  for (unsigned i = 0, i_end = sorts.size(); i < i_end; ++ i) {
     sortNodes.push_back(*sorts[i].d_typeNode);
  }
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkPredicateType(sortNodes)));
}

TupleType ExprManager::mkTupleType(const std::vector<Type>& types) {
  Assert( types.size() >= 2 );
  NodeManagerScope nms(d_nodeManager);
  std::vector<TypeNode> typeNodes;
  for (unsigned i = 0, i_end = types.size(); i < i_end; ++ i) {
     typeNodes.push_back(*types[i].d_typeNode);
  }
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkTupleType(typeNodes)));
}

BitVectorType ExprManager::mkBitVectorType(unsigned size) const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkBitVectorType(size)));
}

ArrayType ExprManager::mkArrayType(Type indexType, Type constituentType) const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkArrayType(*indexType.d_typeNode, *constituentType.d_typeNode)));
}

SortType ExprManager::mkSort(const std::string& name) const {
  NodeManagerScope nms(d_nodeManager);
  return Type(d_nodeManager, new TypeNode(d_nodeManager->mkSort(name)));
}

/**
 * Get the type for the given Expr and optionally do type checking.
 *
 * Initial type computation will be near-constant time if
 * type checking is not requested. Results are memoized, so that
 * subsequent calls to getType() without type checking will be
 * constant time.
 *
 * Initial type checking is linear in the size of the expression.
 * Again, the results are memoized, so that subsequent calls to
 * getType(), with or without type checking, will be constant
 * time.
 *
 * NOTE: A TypeCheckingException can be thrown even when type
 * checking is not requested. getType() will always return a
 * valid and correct type and, thus, an exception will be thrown
 * when no valid or correct type can be computed (e.g., if the
 * arguments to a bit-vector operation aren't bit-vectors). When
 * type checking is not requested, getType() will do the minimum
 * amount of checking required to return a valid result.
 *
 * @param n the Expr for which we want a type
 * @param check whether we should check the type as we compute it 
 * (default: false)
 */
Type ExprManager::getType(const Expr& e, bool check) throw (TypeCheckingException) {
  NodeManagerScope nms(d_nodeManager);
  Type t;
  try {
    t = Type(d_nodeManager, new TypeNode(d_nodeManager->getType(e.getNode(), check)));
  } catch (const TypeCheckingExceptionPrivate& e) {
    throw TypeCheckingException(Expr(this, new Node(e.getNode())), e.getMessage());
  }
  return t;
}

Expr ExprManager::mkVar(const std::string& name, const Type& type) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, d_nodeManager->mkVarPtr(name, *type.d_typeNode));
}

Expr ExprManager::mkVar(const Type& type) {
  NodeManagerScope nms(d_nodeManager);
  return Expr(this, d_nodeManager->mkVarPtr(*type.d_typeNode));
}

Expr ExprManager::mkAssociative(Kind kind,
                                const std::vector<Expr>& children) {
  CheckArgument( kind::isAssociative(kind), kind,
                 "Illegal kind in mkAssociative: %s",
                 kind::kindToString(kind).c_str());

  NodeManagerScope nms(d_nodeManager);
  const unsigned int max = maxArity(kind);
  const unsigned int min = minArity(kind);
  unsigned int numChildren = children.size();

  /* If the number of children is within bounds, then there's nothing to do. */
  if( numChildren <= max ) {
    return mkExpr(kind,children);
  } 

  std::vector<Expr>::const_iterator it = children.begin() ;
  std::vector<Expr>::const_iterator end = children.end() ;

  /* The new top-level children and the children of each sub node */
  std::vector<Node> newChildren;
  std::vector<Node> subChildren;

  while( it != end && numChildren > max ) {
    /* Grab the next max children and make a node for them. */
    for( std::vector<Expr>::const_iterator next = it + max;
         it != next;
         ++it, --numChildren ) {
      subChildren.push_back(it->getNode());
    }
    Node subNode = d_nodeManager->mkNode(kind,subChildren);
    newChildren.push_back(subNode);

    subChildren.clear();
  }

  /* If there's children left, "top off" the Expr. */
  if(numChildren > 0) {
    /* If the leftovers are too few, just copy them into newChildren;
     * otherwise make a new sub-node  */
    if(numChildren < min) {
      for(; it != end; ++it) {
        newChildren.push_back(it->getNode());
      }
    } else {
      for(; it != end; ++it) {
        subChildren.push_back(it->getNode());
      }
      Node subNode = d_nodeManager->mkNode(kind, subChildren);
      newChildren.push_back(subNode);
    }
  }

  /* It's inconceivable we could have enough children for this to fail
   * (more than 2^32, in most cases?). */
  AlwaysAssert( newChildren.size() <= max,
                "Too many new children in mkAssociative" );

  /* It would be really weird if this happened (it would require
   * min > 2, for one thing), but let's make sure. */
  AlwaysAssert( newChildren.size() >= min, 
                "Too few new children in mkAssociative" );

  return Expr(this, d_nodeManager->mkNodePtr(kind,newChildren) );
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
