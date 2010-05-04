/*********************                                                        */
/** type.cpp
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Implementation of expression types 
 **/

#include "expr/node_manager.h"
#include "expr/expr_manager.h"
#include "expr/type.h"
#include "expr/type_node.h"
#include "expr/type_constant.h"
#include "util/Assert.h"
#include <string>

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Type& e) {
  e.toStream(out);
  return out;
}

Type Type::makeType(const TypeNode& typeNode) const
{
  return Type(d_nodeManager, new TypeNode(typeNode));
}

Type::Type(NodeManager* nm, TypeNode* node)
: d_typeNode(node),
  d_nodeManager(nm)
{
}

Type::~Type() {
  NodeManagerScope nms(d_nodeManager);
  delete d_typeNode;
}

Type::Type()
: d_typeNode(new TypeNode()),
  d_nodeManager(NULL)
{
}

Type::Type(uintptr_t n)
: d_typeNode(new TypeNode()),
  d_nodeManager(NULL) {
  AlwaysAssert(n == 0);
}

Type::Type(const Type& t)
: d_typeNode(new TypeNode(*t.d_typeNode)),
  d_nodeManager(t.d_nodeManager)
{
}

bool Type::isNull() const {
  return d_typeNode->isNull();
}

Type& Type::operator=(const Type& t) {
  NodeManagerScope nms(d_nodeManager);
  if (this != &t) {
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

void Type::toStream(std::ostream& out) const {
  NodeManagerScope nms(d_nodeManager);
  out << *d_typeNode;
  return;
}

/** Is this the Boolean type? */
bool Type::isBoolean() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isBoolean();
}

/** Cast to a Boolean type */
Type::operator BooleanType() const throw (AssertionException) {
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
Type::operator IntegerType() const throw (AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isInteger());
  return IntegerType(*this);
}

/** Is this the real type? */
bool Type::isReal() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isInteger();
}

/** Cast to a real type */
Type::operator RealType() const throw (AssertionException) {
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
Type::operator BitVectorType() const throw (AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isBitVector());
  return BitVectorType(*this);
}

/** Is this a function type? */
bool Type::isFunction() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isFunction();
}

/** Is this a predicate type? NOTE: all predicate types are also
    function types. */
bool Type::isPredicate() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isPredicate();
}

/** Cast to a function type */
Type::operator FunctionType() const throw (AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isFunction());
  return FunctionType(*this);
}

/** Is this a sort kind */
bool Type::isSort() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSort();
}

/** Cast to a sort type */
Type::operator SortType() const throw (AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isSort());
  return SortType(*this);
}

/** Is this a kind type (i.e., the type of a type)? */
bool Type::isKind() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isKind();
}

/** Cast to a kind type */
Type::operator KindType() const throw (AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isKind());
  return KindType(*this);
}

std::vector<Type> FunctionType::getArgTypes() const {
  NodeManagerScope nms(d_nodeManager);
  std::vector<Type> args;
  std::vector<TypeNode> argNodes = d_typeNode->getArgTypes();
  std::vector<TypeNode>::iterator it = argNodes.begin();
  std::vector<TypeNode>::iterator it_end = argNodes.end();
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

std::string SortType::getName() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getAttribute(expr::VarNameAttr());
}

BooleanType::BooleanType(const Type& t) throw (AssertionException)
: Type(t)
{
  Assert(isBoolean());
}

IntegerType::IntegerType(const Type& t) throw (AssertionException)
: Type(t)
{
  Assert(isInteger());
}

RealType::RealType(const Type& t) throw (AssertionException)
: Type(t)
{
  Assert(isReal());
}

BitVectorType::BitVectorType(const Type& t) throw (AssertionException)
: Type(t)
{
  Assert(isBitVector());
}

FunctionType::FunctionType(const Type& t) throw (AssertionException)
: Type(t)
{
  Assert(isFunction());
}

KindType::KindType(const Type& t) throw (AssertionException)
: Type(t)
{
  Assert(isKind());
}

SortType::SortType(const Type& t) throw (AssertionException)
: Type(t)
{
  Assert(isSort());
}


unsigned BitVectorType::getSize() const {
  return d_typeNode->getBitVectorSize();
}

}/* CVC4 namespace */
