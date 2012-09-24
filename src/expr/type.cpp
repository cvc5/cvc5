/*********************                                                        */
/*! \file type.cpp
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: dejan, mdeters
 ** Minor contributors (to current version): ajreynol
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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

Type::Type(const Type& t) :
  d_typeNode(new TypeNode(*t.d_typeNode)),
  d_nodeManager(t.d_nodeManager) {
}

bool Type::isNull() const {
  return d_typeNode->isNull();
}

Cardinality Type::getCardinality() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getCardinality();
}

bool Type::isWellFounded() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isWellFounded();
}

Expr Type::mkGroundTerm() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->mkGroundTerm().toExpr();
}

bool Type::isSubtypeOf(Type t) const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSubtypeOf(*t.d_typeNode);
}

bool Type::isComparableTo(Type t) const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isComparableTo(*t.d_typeNode);
}

Type& Type::operator=(const Type& t) {
  Assert(d_typeNode != NULL, "Unexpected NULL typenode pointer!");
  Assert(t.d_typeNode != NULL, "Unexpected NULL typenode pointer!");

  if(this != &t) {
    if(d_nodeManager == t.d_nodeManager) {
      NodeManagerScope nms(d_nodeManager);
      *d_typeNode = *t.d_typeNode;
    } else {
      // This happens more than you think---every time you set to or
      // from the null Type.  It's tricky because each node manager
      // must be in play at the right time.

      NodeManagerScope nms1(d_nodeManager);
      *d_typeNode = TypeNode::null();

      NodeManagerScope nms2(t.d_nodeManager);
      *d_typeNode = *t.d_typeNode;

      d_nodeManager = t.d_nodeManager;
    }
  }
  return *this;
}

bool Type::operator==(const Type& t) const {
  NodeManagerScope nms(d_nodeManager);
  return *d_typeNode == *t.d_typeNode;
}

bool Type::operator!=(const Type& t) const {
  NodeManagerScope nms(d_nodeManager);
  return *d_typeNode != *t.d_typeNode;
}

bool Type::operator<(const Type& t) const {
  NodeManagerScope nms(d_nodeManager);
  return *d_typeNode < *t.d_typeNode;
}

bool Type::operator<=(const Type& t) const {
  NodeManagerScope nms(d_nodeManager);
  return *d_typeNode <= *t.d_typeNode;
}

bool Type::operator>(const Type& t) const {
  NodeManagerScope nms(d_nodeManager);
  return *d_typeNode > *t.d_typeNode;
}

bool Type::operator>=(const Type& t) const {
  NodeManagerScope nms(d_nodeManager);
  return *d_typeNode >= *t.d_typeNode;
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

ExprManager* Type::getExprManager() const {
  return d_nodeManager->toExprManager();
}

Type Type::exportTo(ExprManager* exprManager, ExprManagerMapCollection& vmap) const {
  return ExprManager::exportType(*this, exprManager, vmap);
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
  Assert(isNull() || isBoolean());
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
  Assert(isNull() || isInteger());
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
  Assert(isNull() || isReal());
  return RealType(*this);
}

/** Is this the string type? */
bool Type::isString() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isString();
}

/** Cast to a string type */
Type::operator StringType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isNull() || isString());
  return StringType(*this);
}

/** Is this the bit-vector type? */
bool Type::isBitVector() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isBitVector();
}

/** Cast to a bit-vector type */
Type::operator BitVectorType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isNull() || isBitVector());
  return BitVectorType(*this);
}

/** Cast to a Constructor type */
Type::operator DatatypeType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isNull() || isDatatype());
  return DatatypeType(*this);
}

/** Is this a datatype type? */
bool Type::isDatatype() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isDatatype() || d_typeNode->isParametricDatatype();
}

/** Cast to a Constructor type */
Type::operator ConstructorType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isNull() || isConstructor());
  return ConstructorType(*this);
}

/** Is this the Constructor type? */
bool Type::isConstructor() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isConstructor();
}

/** Cast to a Selector type */
Type::operator SelectorType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isNull() || isSelector());
  return SelectorType(*this);
}

/** Is this the Selector type? */
bool Type::isSelector() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSelector();
}

/** Cast to a Tester type */
Type::operator TesterType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isNull() || isTester());
  return TesterType(*this);
}

/** Is this the Tester type? */
bool Type::isTester() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isTester();
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
  Assert(isNull() || isFunction());
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
  Assert(isNull() || isTuple());
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
  Assert(isNull() || isSort());
  return SortType(*this);
}

/** Is this a sort constructor kind */
bool Type::isSortConstructor() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSortConstructor();
}

/** Cast to a sort constructor type */
Type::operator SortConstructorType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isNull() || isSortConstructor());
  return SortConstructorType(*this);
}

/** Is this a predicate subtype */
bool Type::isPredicateSubtype() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isPredicateSubtype();
}

/** Cast to a predicate subtype */
Type::operator PredicateSubtype() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isNull() || isPredicateSubtype());
  return PredicateSubtype(*this);
}

/** Is this an integer subrange */
bool Type::isSubrange() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSubrange();
}

/** Cast to a predicate subtype */
Type::operator SubrangeType() const throw(AssertionException) {
  NodeManagerScope nms(d_nodeManager);
  Assert(isNull() || isSubrange());
  return SubrangeType(*this);
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
  Assert(isNull() || isFunction());
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

bool SortType::isParameterized() const {
  return false;
}

/** Get the parameter types */
std::vector<Type> SortType::getParamTypes() const {
  vector<Type> params;
  return params;
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
  Assert(isNull() || isBoolean());
}

IntegerType::IntegerType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isInteger());
}

RealType::RealType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isReal());
}

StringType::StringType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isString());
}

BitVectorType::BitVectorType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isBitVector());
}

DatatypeType::DatatypeType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isDatatype());
}

ConstructorType::ConstructorType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isConstructor());
}

SelectorType::SelectorType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isSelector());
}

TesterType::TesterType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isTester());
}

FunctionType::FunctionType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isFunction());
}

TupleType::TupleType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isTuple());
}

ArrayType::ArrayType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isArray());
}

SortType::SortType(const Type& t) throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isSort());
}

SortConstructorType::SortConstructorType(const Type& t)
  throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isSortConstructor());
}

PredicateSubtype::PredicateSubtype(const Type& t)
  throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isPredicateSubtype());
}

SubrangeType::SubrangeType(const Type& t)
  throw(AssertionException) :
  Type(t) {
  Assert(isNull() || isSubrange());
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

DatatypeType ConstructorType::getRangeType() const {
  return DatatypeType(makeType(d_typeNode->getConstructorRangeType()));
}

size_t ConstructorType::getArity() const {
  return d_typeNode->getNumChildren() - 1;
}

std::vector<Type> ConstructorType::getArgTypes() const {
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

const Datatype& DatatypeType::getDatatype() const {
  if( d_typeNode->isParametricDatatype() ) {
    Assert( (*d_typeNode)[0].getKind() == kind::DATATYPE_TYPE );
    const Datatype& dt = (*d_typeNode)[0].getConst<Datatype>();
    return dt;
  } else {
    return d_typeNode->getConst<Datatype>();
  }
}

bool DatatypeType::isParametric() const {
  return d_typeNode->isParametricDatatype();
}

Expr DatatypeType::getConstructor(std::string name) const {
  return getDatatype().getConstructor(name);
}

bool DatatypeType::isInstantiated() const {
  return d_typeNode->isInstantiatedDatatype();
}

bool DatatypeType::isParameterInstantiated(unsigned n) const {
  return d_typeNode->isParameterInstantiatedDatatype(n);
}

size_t DatatypeType::getArity() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getNumChildren() - 1;
}

std::vector<Type> DatatypeType::getParamTypes() const {
  NodeManagerScope nms(d_nodeManager);
  vector<Type> params;
  vector<TypeNode> paramNodes = d_typeNode->getParamTypes();
  vector<TypeNode>::iterator it = paramNodes.begin();
  vector<TypeNode>::iterator it_end = paramNodes.end();
  for(; it != it_end; ++it) {
    params.push_back(makeType(*it));
  }
  return params;
}

DatatypeType DatatypeType::instantiate(const std::vector<Type>& params) const {
  NodeManagerScope nms(d_nodeManager);
  TypeNode cons = d_nodeManager->mkTypeConst( getDatatype() );
  vector<TypeNode> paramsNodes;
  paramsNodes.push_back( cons );
  for(vector<Type>::const_iterator i = params.begin(),
        iend = params.end();
      i != iend;
      ++i) {
    paramsNodes.push_back(*getTypeNode(*i));
  }
  return DatatypeType(makeType(d_nodeManager->mkTypeNode(kind::PARAMETRIC_DATATYPE,paramsNodes)));
}

DatatypeType SelectorType::getDomain() const {
  return DatatypeType(makeType((*d_typeNode)[0]));
}

Type SelectorType::getRangeType() const {
  return makeType((*d_typeNode)[1]);
}

DatatypeType TesterType::getDomain() const {
  return DatatypeType(makeType((*d_typeNode)[0]));
}

BooleanType TesterType::getRangeType() const {
  return BooleanType(makeType(d_nodeManager->booleanType()));
}

Expr PredicateSubtype::getPredicate() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getSubtypePredicate().toExpr();
}

Type PredicateSubtype::getBaseType() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getSubtypeBaseType().toType();
}

SubrangeBounds SubrangeType::getSubrangeBounds() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getSubrangeBounds();
}

size_t TypeHashFunction::operator()(const Type& t) const {
  return TypeNodeHashFunction()(NodeManager::fromType(t));
}

}/* CVC4 namespace */
