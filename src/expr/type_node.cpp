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
    case PSEUDOBOOLEAN_TYPE:
      return t.getKind() == kind::TYPE_CONSTANT &&
        ( t.getConst<TypeConstant>() == BOOLEAN_TYPE ||
          t.getConst<TypeConstant>() == INTEGER_TYPE );
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

}/* CVC4 namespace */
