/*********************                                                        */
/*! \file type_node.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking, ajreynol
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Reference-counted encapsulation of a pointer to node information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include <vector>

#include "expr/type_node.h"
#include "expr/type_properties.h"

using namespace std;

namespace CVC4 {

TypeNode TypeNode::s_null( &expr::NodeValue::s_null );

TypeNode TypeNode::substitute(const TypeNode& type,
                              const TypeNode& replacement,
                              std::hash_map<TypeNode, TypeNode, HashFunction>& cache) const {
  // in cache?
  std::hash_map<TypeNode, TypeNode, HashFunction>::const_iterator i = cache.find(*this);
  if(i != cache.end()) {
    return (*i).second;
  }

  // otherwise compute
  NodeBuilder<> nb(getKind());
  if(getMetaKind() == kind::metakind::PARAMETERIZED) {
    // push the operator
    nb << TypeNode(d_nv->d_children[0]);
  }
  for(TypeNode::const_iterator i = begin(),
        iend = end();
      i != iend;
      ++i) {
    if(*i == type) {
      nb << replacement;
    } else {
      (*i).substitute(type, replacement);
    }
  }

  // put in cache
  TypeNode tn = nb.constructTypeNode();
  cache[*this] = tn;
  return tn;
}

Cardinality TypeNode::getCardinality() const {
  return kind::getCardinality(*this);
}

bool TypeNode::isWellFounded() const {
  return kind::isWellFounded(*this);
}

Node TypeNode::mkGroundTerm() const {
  return kind::mkGroundTerm(*this);
}

bool TypeNode::isSubtypeOf(TypeNode t) const {
  if(*this == t) {
    return true;
  }
  if(getKind() == kind::TYPE_CONSTANT) {
    switch(getConst<TypeConstant>()) {
    case INTEGER_TYPE:
      return t.getKind() == kind::TYPE_CONSTANT && t.getConst<TypeConstant>() == REAL_TYPE;
    default:
      return false;
    }
  }
  if(isSubrange()) {
    if(t.isSubrange()) {
      return t.getSubrangeBounds() <= getSubrangeBounds();
    } else {
      return t.getKind() == kind::TYPE_CONSTANT &&
        ( t.getConst<TypeConstant>() == INTEGER_TYPE ||
          t.getConst<TypeConstant>() == REAL_TYPE );
    }
  }
  if(isPredicateSubtype()) {
    return getSubtypeBaseType().isSubtypeOf(t);
  }
  return false;
}

bool TypeNode::isComparableTo(TypeNode t) const {
  if(*this == t) {
    return true;
  }
  if(isSubtypeOf(NodeManager::currentNM()->realType())) {
    return t.isSubtypeOf(NodeManager::currentNM()->realType());
  }
  if(isPredicateSubtype()) {
    return t.isComparableTo(getSubtypeBaseType());
  }
  return false;
}

Node TypeNode::getSubtypePredicate() const {
  Assert(isPredicateSubtype());
  return Node::fromExpr(getConst<Predicate>());
}

TypeNode TypeNode::getSubtypeBaseType() const {
  Assert(isPredicateSubtype());
  return getSubtypePredicate().getType().getArgTypes()[0];
}

std::vector<TypeNode> TypeNode::getArgTypes() const {
  vector<TypeNode> args;
  if(isTester()) {
    Assert(getNumChildren() == 1);
    args.push_back((*this)[0]);
  } else {
    Assert(isFunction() || isConstructor() || isSelector());
    for(unsigned i = 0, i_end = getNumChildren() - 1; i < i_end; ++i) {
      args.push_back((*this)[i]);
    }
  }
  return args;
}

std::vector<TypeNode> TypeNode::getParamTypes() const {
  vector<TypeNode> params;
  Assert(isParametricDatatype());
  for(unsigned i = 1, i_end = getNumChildren(); i < i_end; ++i) {
    params.push_back((*this)[i]);
  }
  return params;
}

/** Is this a tuple type? */
vector<TypeNode> TypeNode::getTupleTypes() const {
  Assert(isTuple());
  vector<TypeNode> types;
  for(unsigned i = 0, i_end = getNumChildren(); i < i_end; ++i) {
    types.push_back((*this)[i]);
  }
  return types;
}

/** Is this an instantiated datatype type */
bool TypeNode::isInstantiatedDatatype() const {
  if(getKind() == kind::DATATYPE_TYPE) {
    return true;
  }
  if(getKind() != kind::PARAMETRIC_DATATYPE) {
    return false;
  }
  const Datatype& dt = (*this)[0].getConst<Datatype>();
  unsigned n = dt.getNumParameters();
  Assert(n < getNumChildren());
  for(unsigned i = 0; i < n; ++i) {
    if(TypeNode::fromType(dt.getParameter(i)) == (*this)[i + 1]) {
      return false;
    }
  }
  return true;
}

/** Is this an instantiated datatype parameter */
bool TypeNode::isParameterInstantiatedDatatype(unsigned n) const {
  AssertArgument(getKind() == kind::PARAMETRIC_DATATYPE, *this);
  const Datatype& dt = (*this)[0].getConst<Datatype>();
  AssertArgument(n < dt.getNumParameters(), *this);
  return TypeNode::fromType(dt.getParameter(n)) != (*this)[n + 1];
}

TypeNode TypeNode::leastCommonTypeNode(TypeNode t0, TypeNode t1){
  Assert( NodeManager::currentNM() != NULL,
          "There is no current CVC4::NodeManager associated to this thread.\n"
          "Perhaps a public-facing function is missing a NodeManagerScope ?" );

  Assert(!t0.isNull());
  Assert(!t1.isNull());

  if(EXPECT_TRUE(t0 == t1)){
    return t0;
  }else{ // t0 != t1
    if(t0.getKind()== kind::TYPE_CONSTANT){
      switch(t0.getConst<TypeConstant>()) {
      case INTEGER_TYPE:
        if(t1.isInteger()){
          // t0 == IntegerType && t1.isInteger()
          return t0; //IntegerType
        }else if(t1.isReal()){
          // t0 == IntegerType && t1.isReal() && !t1.isInteger()
          return NodeManager::currentNM()->realType(); // RealType
        }else{
          return TypeNode(); //null type
        }
      case REAL_TYPE:
        if(t1.isReal()){
          return t0; // RealType
        }else{
          return TypeNode(); // null type
        }
      default:
        if(t1.isPredicateSubtype() && t1.getSubtypeBaseType().isSubtypeOf(t0)){
          return t0; // t0 is a constant type
        }else{
          return TypeNode(); // null type
        }
      }
    }else if(t1.getKind() == kind::TYPE_CONSTANT){
      return leastCommonTypeNode(t1, t0); //decrease the number of special cases
    }else{
      // t0 != t1 &&
      // t0.getKind() == kind::TYPE_CONSTANT &&
      // t1.getKind() == kind::TYPE_CONSTANT
      switch(t0.getKind()){
      case kind::ARRAY_TYPE:
      case kind::BITVECTOR_TYPE:
      case kind::SORT_TYPE:
      case kind::PARAMETRIC_DATATYPE:
      case kind::CONSTRUCTOR_TYPE:
      case kind::SELECTOR_TYPE:
      case kind::TESTER_TYPE:
        if(t1.isPredicateSubtype() && t1.getSubtypeBaseType().isSubtypeOf(t0)){
          return t0;
        }else{
          return TypeNode();
        }
      case kind::FUNCTION_TYPE:
        return TypeNode(); // Not sure if this is right
      case kind::TUPLE_TYPE:
        Unimplemented("haven't implemented leastCommonType for tuples yet");
        return TypeNode(); // Not sure if this is right
      case kind::SUBTYPE_TYPE:
        if(t1.isPredicateSubtype()){
          // This is the case where both t0 and t1 are predicate subtypes.
          return leastCommonPredicateSubtype(t0, t1);
        }else{ //t0 is a predicate subtype and t1 is not
          return leastCommonTypeNode(t1, t0); //decrease the number of special cases
        }
      case kind::SUBRANGE_TYPE:
        if(t1.isSubrange()){
          const SubrangeBounds& t0SR= t0.getSubrangeBounds();
          const SubrangeBounds& t1SR = t1.getSubrangeBounds();
          if(SubrangeBounds::joinIsBounded(t0SR, t1SR)){
            SubrangeBounds j = SubrangeBounds::join(t0SR, t1SR);
            return NodeManager::currentNM()->mkSubrangeType(j);
          }else{
            return NodeManager::currentNM()->integerType();
          }
        }else if(t1.isPredicateSubtype()){
          //t0 is a subrange
          //t1 is not a subrange
          //t1 is a predicate subtype
          if(t1.isInteger()){
            return NodeManager::currentNM()->integerType();
          }else if(t1.isReal()){
            return NodeManager::currentNM()->realType();
          }else{
            return TypeNode();
          }
        }else{
          //t0 is a subrange
          //t1 is not a subrange
          // t1 is not a type constant && is not a predicate subtype
          // t1 cannot be real subtype or integer.
          Assert(t1.isReal());
          Assert(t1.isInteger());
          return TypeNode();
        }
      case kind::DATATYPE_TYPE:
        // two datatypes that aren't == have no common ancestors
        return TypeNode();
      default:
        Unimplemented("don't have a leastCommonType for types `%s' and `%s'", t0.toString().c_str(), t1.toString().c_str());
        return TypeNode();
      }
    }
  }
}

TypeNode TypeNode::leastCommonPredicateSubtype(TypeNode t0, TypeNode t1){
  Assert(t0.isPredicateSubtype());
  Assert(t1.isPredicateSubtype());

  std::vector<TypeNode> t0stack;
  t0stack.push_back(t0);
  while(t0stack.back().isPredicateSubtype()){
    t0stack.push_back(t0stack.back().getSubtypeBaseType());
  }
  std::vector<TypeNode> t1stack;
  t1stack.push_back(t1);
  while(t1stack.back().isPredicateSubtype()){
    t1stack.push_back(t1stack.back().getSubtypeBaseType());
  }

  Assert(!t0stack.empty());
  Assert(!t1stack.empty());

  if(t0stack.back() == t1stack.back()){
    TypeNode mostGeneral = t1stack.back();
    t0stack.pop_back(); t1stack.pop_back();
    while(!t0stack.empty() && t1stack.empty() && t0stack.back() == t1stack.back()){
      mostGeneral = t0stack.back();
      t0stack.pop_back(); t1stack.pop_back();
    }
    return mostGeneral;
  }else{
    return leastCommonTypeNode(t0stack.back(), t1stack.back());
  }
}

}/* CVC4 namespace */
