/*********************                                                        */
/*! \file type.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Dejan Jovanovic, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of expression types
 **
 ** Implementation of expression types.
 **/
#include "expr/type.h"

#include <iostream>
#include <string>
#include <vector>

#include "base/exception.h"
#include "expr/node_manager.h"
#include "expr/node_manager_attributes.h"
#include "expr/type_node.h"

using namespace std;

namespace CVC4 {

ostream& operator<<(ostream& out, const Type& t) {
  NodeManagerScope nms(t.d_nodeManager);
  return out << *Type::getTypeNode(t);
}

Type Type::makeType(const TypeNode& typeNode) const {
  return Type(d_nodeManager, new TypeNode(typeNode));
}

Type::Type(NodeManager* nm, TypeNode* node)
    : d_typeNode(node), d_nodeManager(nm) {
  // This does not require a NodeManagerScope as this is restricted to be an
  // internal only pointer initialization call.
}

Type::Type() : d_typeNode(new TypeNode), d_nodeManager(NULL) {
  // This does not require a NodeManagerScope as `new TypeNode` is backed by a
  // static expr::NodeValue::null().
}

Type::Type(const Type& t) : d_typeNode(NULL), d_nodeManager(t.d_nodeManager) {
  NodeManagerScope nms(d_nodeManager);
  d_typeNode = new TypeNode(*t.d_typeNode);
}

Type::~Type() {
  NodeManagerScope nms(d_nodeManager);
  delete d_typeNode;
}

bool Type::isNull() const {
  return d_typeNode->isNull();
}

Cardinality Type::getCardinality() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getCardinality();
}

bool Type::isFinite() const
{
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isFinite();
}

bool Type::isInterpretedFinite() const
{
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isInterpretedFinite();
}

bool Type::isWellFounded() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isWellFounded();
}

bool Type::isFirstClass() const
{
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isFirstClass();
}

bool Type::isFunctionLike() const
{
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isFunctionLike();
}

Expr Type::mkGroundTerm() const {
  NodeManagerScope nms(d_nodeManager);
  Expr ret = d_typeNode->mkGroundTerm().toExpr();
  if (ret.isNull())
  {
    IllegalArgument(this, "Cannot construct ground term!");
  }
  return ret;
}

Expr Type::mkGroundValue() const
{
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->mkGroundValue().toExpr();
}

bool Type::isSubtypeOf(Type t) const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSubtypeOf(*t.d_typeNode);
}

bool Type::isComparableTo(Type t) const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isComparableTo(*t.d_typeNode);
}

Type Type::getBaseType() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getBaseType().toType();
}

Type& Type::operator=(const Type& t) {
  PrettyCheckArgument(d_typeNode != NULL, this, "Unexpected NULL typenode pointer!");
  PrettyCheckArgument(t.d_typeNode != NULL, t, "Unexpected NULL typenode pointer!");

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

/** Is this the integer type? */
bool Type::isInteger() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isInteger();
}

/** Is this the real type? */
bool Type::isReal() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isReal();
}

/** Is this the string type? */
bool Type::isString() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isString();
}

/** Is this the regexp type? */
bool Type::isRegExp() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isRegExp();
}

/** Is this the rounding mode type? */
bool Type::isRoundingMode() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isRoundingMode();
}

/** Is this the bit-vector type? */
bool Type::isBitVector() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isBitVector();
}

/** Is this the floating-point type? */
bool Type::isFloatingPoint() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isFloatingPoint();
}

/** Is this a datatype type? */
bool Type::isDatatype() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isDatatype();
}

/** Is this the Constructor type? */
bool Type::isConstructor() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isConstructor();
}

/** Is this the Selector type? */
bool Type::isSelector() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSelector();
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

/** Is this a tuple type? */
bool Type::isTuple() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isTuple();
}

/** Is this a record type? */
bool Type::isRecord() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getKind() == kind::DATATYPE_TYPE
         && DatatypeType(*this).getDatatype().isRecord();
}

/** Is this a symbolic expression type? */
bool Type::isSExpr() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSExpr();
}

/** Is this an array type? */
bool Type::isArray() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isArray();
}

/** Is this a Set type? */
bool Type::isSet() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSet();
}

bool Type::isSequence() const
{
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSequence();
}

/** Is this a sort kind */
bool Type::isSort() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSort();
}

/** Cast to a sort type */
bool Type::isSortConstructor() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->isSortConstructor();
}

size_t FunctionType::getArity() const {
  return d_typeNode->getNumChildren() - 1;
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
  PrettyCheckArgument(isNull() || isFunction(), this);
  return makeType(d_typeNode->getRangeType());
}

vector<Type> SExprType::getTypes() const {
  NodeManagerScope nms(d_nodeManager);
  vector<Type> types;
  vector<TypeNode> typeNodes = d_typeNode->getSExprTypes();
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

BooleanType::BooleanType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isBoolean(), this);
}

IntegerType::IntegerType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isInteger(), this);
}

RealType::RealType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isReal(), this);
}

StringType::StringType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isString(), this);
}

RegExpType::RegExpType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isRegExp(), this);
}

RoundingModeType::RoundingModeType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isRoundingMode(), this);
}

BitVectorType::BitVectorType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isBitVector(), this);
}

FloatingPointType::FloatingPointType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isFloatingPoint(), this);
}

DatatypeType::DatatypeType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isDatatype(), this);
}

ConstructorType::ConstructorType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isConstructor(), this);
}

SelectorType::SelectorType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isSelector(), this);
}

TesterType::TesterType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isTester(), this);
}

FunctionType::FunctionType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isFunction(), this);
}

SExprType::SExprType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isSExpr(), this);
}

ArrayType::ArrayType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isArray(), this);
}

SetType::SetType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isSet(), this);
}

SequenceType::SequenceType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isSequence(), this);
}

SortType::SortType(const Type& t) : Type(t)
{
  PrettyCheckArgument(isNull() || isSort(), this);
}

SortConstructorType::SortConstructorType(const Type& t)
    : Type(t) {
  PrettyCheckArgument(isNull() || isSortConstructor(), this);
}

unsigned BitVectorType::getSize() const {
  return d_typeNode->getBitVectorSize();
}

unsigned FloatingPointType::getExponentSize() const {
  return d_typeNode->getFloatingPointExponentSize();
}

unsigned FloatingPointType::getSignificandSize() const {
  return d_typeNode->getFloatingPointSignificandSize();
}

Type ArrayType::getIndexType() const {
  return makeType(d_typeNode->getArrayIndexType());
}

Type ArrayType::getConstituentType() const {
  return makeType(d_typeNode->getArrayConstituentType());
}

Type SetType::getElementType() const {
  return makeType(d_typeNode->getSetElementType());
}

Type SequenceType::getElementType() const
{
  return makeType(d_typeNode->getSequenceElementType());
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
  NodeManagerScope nms(d_nodeManager);
  Assert(isDatatype());
  if (d_typeNode->getKind() == kind::DATATYPE_TYPE)
  {
    DatatypeIndexConstant dic = d_typeNode->getConst<DatatypeIndexConstant>();
    return d_nodeManager->toExprManager()->getDatatypeForIndex(dic.getIndex());
  }
  Assert(d_typeNode->getKind() == kind::PARAMETRIC_DATATYPE);
  return DatatypeType((*d_typeNode)[0].toType()).getDatatype();
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
  TypeNode cons = d_nodeManager->mkTypeConst( (*d_typeNode)[0].getConst<DatatypeIndexConstant>() );
  vector<TypeNode> paramsNodes;
  paramsNodes.push_back( cons );
  for(vector<Type>::const_iterator i = params.begin(),
        iend = params.end();
      i != iend;
      ++i) {
    paramsNodes.push_back(*getTypeNode(*i));
  }
  return DatatypeType(makeType(d_nodeManager->mkTypeNode(kind::PARAMETRIC_DATATYPE, paramsNodes)));
}

/** Get the length of a tuple type */
size_t DatatypeType::getTupleLength() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getTupleLength();
}

/** Get the constituent types of a tuple type */
std::vector<Type> DatatypeType::getTupleTypes() const {
  NodeManagerScope nms(d_nodeManager);
  std::vector< TypeNode > vec = d_typeNode->getTupleTypes();
  std::vector< Type > vect;
  for( unsigned i=0; i<vec.size(); i++ ){
    vect.push_back( vec[i].toType() );
  }
  return vect;
}

/** Get the description of the record type */
const Record& DatatypeType::getRecord() const {
  NodeManagerScope nms(d_nodeManager);
  Assert(isRecord());
  const Datatype& dt = getDatatype();
  return *(dt.getRecord());
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

/* - not in release 1.0
Expr PredicateSubtype::getPredicate() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getSubtypePredicate().toExpr();
}

Type PredicateSubtype::getParentType() const {
  NodeManagerScope nms(d_nodeManager);
  return d_typeNode->getSubtypeParentType().toType();
}
*/

size_t TypeHashFunction::operator()(const Type& t) const {
  return TypeNodeHashFunction()(NodeManager::fromType(t));
}

}/* CVC4 namespace */
