/*********************                                                        */
/*! \file type.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters, dejan
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of expression types
 **
 ** Implementation of expression types.
 **/

#include <iostream>
#include <string>
#include <vector>

#include "expr/node_manager.h"
#include "expr/type.h"
#include "expr/type_node.h"
#include "util/Assert.h"

using namespace std;

namespace CVC4 {

ostream& operator<<(ostream& out, const Type& t) {
  NodeManagerScope nms(t.d_nodeManager);
  return out << *Type::getTypeNode(t);
}

Type Type::makeType(const TypeNode& typeNode) const {
  return Type(d_nodeManager, new TypeNode(typeNode));
}

Type::Type(NodeManager* nm, TypeNode* node) :
  d_typeNode(node),
  d_nodeManager(nm) {
}

Type::~Type() {
  NodeManagerScope nms(d_nodeManager);
  delete d_typeNode;
}

Type::Type() :
  d_typeNode(new TypeNode),
  d_nodeManager(NULL) {
}

Type::Type(uintptr_t n) :
  d_typeNode(new TypeNode),
  d_nodeManager(NULL) {
  AlwaysAssert(n == 0);
}

Type::Type(const Type& t) :
  d_typeNode(new TypeNode(*t.d_typeNode)),
  d_nodeManager(t.d_nodeManager) {
}

bool Type::isNull() const {
  return d_typeNode->isNull();
}

Type& Type::operator=(const Type& t) {
  NodeManagerScope nms(d_nodeManager);
  if(this != &t) {
    *d_typeNode = *t.d_typeNode;
    d_nodeManager = t.d_nodeManager;
  }
  return *this;
}

bool Type::operator==(const Type& t) const {
  return *d_typeNode == *t.d_typeNode;
}

bool Type::operator!=(const Type& t) const {
  return *d_typeNode != *t.d_typeNode;
}

Type Type::substitute(const Type& type, const Type& replacement) const {
  NodeManagerScope nms(d_nodeManager);
  return makeType(d_typeNode->substitute(*type.d_typeNode,
                                         *replacement.d_typeNode));
}

Type Type::substitute(const std::vector<Type>& types,
                      const std::vector<Type>& replacements) const {
  NodeManagerScope nms(d_nodeManager);

  vector<TypeNode> typesNodes, replacementsNodes;

  for(vector<Type>::const_iterator i = types.begin(),
        iend = types.end();
      i != iend;
      ++i) {
    typesNodes.push_back(*(*i).d_typeNode);
  }

  for(vector<Type>::const_iterator i = replacements.begin(),
        iend = replacements.end();
      i != iend;
      ++i) {
    replacementsNodes.push_back(*(*i).d_typeNode);
  }

  return makeType(d_typeNode->substitute(typesNodes.begin(),
                                         typesNodes.end(),
                                         replacementsNodes.begin(),
                                         replacementsNodes.end()));
}

void Type::toStream(std::ostream& out) const {
  NodeManagerScope nms(d_nodeManager);
  out << *d_typeNode;
  return;
}

string Type::toString() const {
  NodeManagerScope nms(d_nodeManager);
  stringstream ss;
  ss << *d_typeNode;
  return ss.str();
}

/** Is this the Boolean type? */
bool Type::isBoolean() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isBoolean();
}

/** Cast to a Boolean type */
Type::operator BooleanType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isBoolean());
  return BooleanType(*this);
}

/** Is this the integer type? */
bool Type::isInteger() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isInteger();
}

/** Cast to a integer type */
Type::operator IntegerType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isInteger());
  return IntegerType(*this);
}

/** Is this the real type? */
bool Type::isReal() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isReal();
}

/** Cast to a real type */
Type::operator RealType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isReal());
  return RealType(*this);
}

/** Is this the bit-vector type? */
bool Type::isBitVector() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isBitVector();
}

/** Cast to a bit-vector type */
Type::operator BitVectorType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isBitVector());
  return BitVectorType(*this);
}

/** Is this a function type? */
bool Type::isFunction() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isFunction();
}

/**
 * Is this a predicate type? NOTE: all predicate types are also
 * function types.
 */
bool Type::isPredicate() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isPredicate();
}

/** Cast to a function type */
Type::operator FunctionType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isFunction());
  return FunctionType(*this);
}

/** Is this a tuple type? */
bool Type::isTuple() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isTuple();
}

/** Cast to a tuple type */
Type::operator TupleType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isTuple());
  return TupleType(*this);
}

/** Is this an array type? */
bool Type::isArray() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isArray();
}

/** Cast to an array type */
Type::operator ArrayType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  return ArrayType(*this);
}

/** Is this a sort kind */
bool Type::isSort() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSort();
}

/** Cast to a sort type */
Type::operator SortType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isSort());
  return SortType(*this);
}

/** Is this a sort constructor kind */
bool Type::isSortConstructor() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSortConstructor();
}

/** Cast to a sort type */
Type::operator SortConstructorType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isSortConstructor());
  return SortConstructorType(*this);
}

/** Is this a kind type (i.e., the type of a type)? */
bool Type::isKind() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isKind();
}

/** Cast to a kind type */
Type::operator KindType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isKind());
  return KindType(*this);
}

vector<Type> FunctionType::getArgTypes() const {
  NodeManagerScope nms(d_nodeManager);
  vector<Type> args;
  vector<TypeNode> argNodes = d_typeNode->getArgTypes();
  vector<TypeNode>::iterator it = argNodes.begin();
  vector<TypeNode>::iterator it_end = argNodes.end();
  for(; it != it_end; ++ it) {
    args.push_back(makeType(*it));
  }
  return args;
}

Type FunctionType::getRangeType() const {
  NodeManagerScope nms(d_nodeManager);
  Assert(isFunction());
  return makeType(d_typeNode->getRangeType());
}

vector<Type> TupleType::getTypes() const {
  NodeManagerScope nms(d_nodeManager);
  vector<Type> types;
  vector<TypeNode> typeNodes = d_typeNode->getTupleTypes();
  vector<TypeNode>::iterator it = typeNodes.begin();
  vector<TypeNode>::iterator it_end = typeNodes.end();
  for(; it != it_end; ++ it) {
    types.push_back(makeType(*it));
  }
  return types;
}

string SortType::getName() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getAttribute(expr::VarNameAttr());
}

string SortConstructorType::getName() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getAttribute(expr::VarNameAttr());
}

size_t SortConstructorType::getArity() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getAttribute(expr::SortArityAttr());
}

SortType SortConstructorType::instantiate(const std::vector<Type>& params) const {
  NodeManagerScope nms(d_nodeManager);
  vector<TypeNode> paramsNodes;
  for(vector<Type>::const_iterator i = params.begin(),
        iend = params.end();
      i != iend;
      ++i) {
    paramsNodes.push_back(*getTypeNode(*i));
  }
  return SortType(makeType(d_nodeManager->mkSort(*d_typeNode, paramsNodes)));
}

BooleanType::BooleanType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isBoolean());
}

IntegerType::IntegerType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isInteger());
}

RealType::RealType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isReal());
}

BitVectorType::BitVectorType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isBitVector());
}

FunctionType::FunctionType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isFunction());
}

TupleType::TupleType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isTuple());
}

ArrayType::ArrayType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isArray());
}

KindType::KindType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isKind());
}

SortType::SortType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isSort());
}

SortConstructorType::SortConstructorType(const Type& t)
  throw(AssertionException) :
  Type(t) {
  Assert(isSortConstructor());
}

unsigned BitVectorType::getSize() const {
  return d_typeNode->getBitVectorSize();
}

Type ArrayType::getIndexType() const {
  return makeType(d_typeNode->getArrayIndexType());
}

Type ArrayType::getConstituentType() const {
  return makeType(d_typeNode->getArrayConstituentType());
}

size_t TypeHashStrategy::hash(const Type& t) {
  return TypeNodeHashStrategy::hash(*t.d_typeNode);
}

}/* CVC4 namespace */
