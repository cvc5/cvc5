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
  // Do the cast by hand
  if (isBoolean()) { out << (BooleanType)*this; return; }
  if (isFunction()) { out << (FunctionType)*this; return; }
  if (isKind()) { out << (KindType)*this; return; }
  if (isSort()) { out << (SortType)*this; return; }
  // We should not get here
  Unreachable("Type not implemented completely");
}

/** Is this the Boolean type? */
bool Type::isBoolean() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isBoolean();
}

/** Cast to a Boolean type */
Type::operator BooleanType() const {
  NodeManagerScope nms(d_nodeManager);
  Assert(isBoolean());
  return BooleanType(*this);
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
Type::operator FunctionType() const {
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
Type::operator SortType() const {
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
Type::operator KindType() const {
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

void BooleanType::toStream(std::ostream& out) const {
  out << "BOOLEAN";
}

std::string SortType::getName() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getAttribute(expr::VarNameAttr());
}

void SortType::toStream(std::ostream& out) const {
  NodeManagerScope nms(d_nodeManager);
  out << getName();
}

void FunctionType::toStream(std::ostream& out) const {
  NodeManagerScope nms(d_nodeManager);
  unsigned arity = d_typeNode->getNumChildren();

  if(arity > 2) {
    out << "(";
  }
  unsigned int i;
  for(i=0; i < arity - 1; ++i) {
    if(i > 0) {
      out << ",";
    }
    out << makeType((*d_typeNode)[i]);
  }
  if(arity > 2) {
    out << ")";
  }
  out << " -> ";
  (*d_typeNode)[i].toStream(out);
}

BooleanType::BooleanType(const Type& t) : Type(t) {}
FunctionType::FunctionType(const Type& t) : Type(t) {}
KindType::KindType(const Type& t) : Type(t) {}
SortType::SortType(const Type& t) : Type(t) {}


}/* CVC4 namespace */
