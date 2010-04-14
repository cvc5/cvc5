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
#include "expr/type_constant.h"
#include "util/Assert.h"
#include <string>

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const Type& e) {
  e.toStream(out);
  return out;
}

Type Type::makeType(NodeTemplate<false> typeNode) const
{
  return Type(d_nodeManager, new Node(typeNode));
}

Type::Type(NodeManager* nm, NodeTemplate<true>* node)
: d_typeNode(node),
  d_nodeManager(nm)
{
}

Type::~Type() {
  NodeManagerScope nms(d_nodeManager);
  delete d_typeNode;
}

Type::Type()
: d_typeNode(new Node()),
  d_nodeManager(NULL)
{
}

Type::Type(uintptr_t n)
: d_typeNode(new Node()),
  d_nodeManager(NULL) {
  AlwaysAssert(n == 0);
}

Type::Type(const Type& t)
: d_typeNode(new Node(*t.d_typeNode)),
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
  return d_typeNode->getKind() == kind::TYPE_CONSTANT
      && d_typeNode->getConst<TypeConstant>() == BOOLEAN_TYPE;
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
  return d_typeNode->getKind() == kind::FUNCTION_TYPE;
}

/** Is this a predicate type? NOTE: all predicate types are also
    function types. */
bool Type::isPredicate() const {
  NodeManagerScope nms(d_nodeManager);
  return isFunction() && ((FunctionType)*this).getRangeType().isBoolean();
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
  return d_typeNode->getKind() == kind::VARIABLE &&
      d_typeNode->getType().isKind();
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
  return d_typeNode->getKind() == kind::TYPE_CONSTANT
      && d_typeNode->getConst<TypeConstant>() == KIND_TYPE;
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
  for (unsigned i = 0, i_end = d_typeNode->getNumChildren() - 1; i < i_end; ++ i) {
    args.push_back(makeType((*d_typeNode)[i]));
  }
  return args;
}

Type FunctionType::getRangeType() const {
  NodeManagerScope nms(d_nodeManager);
  return makeType((*d_typeNode)[d_typeNode->getNumChildren()-1]);
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
