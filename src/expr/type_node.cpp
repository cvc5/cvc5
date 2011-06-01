/*********************                                                        */
/*! \file type_node.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
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

bool TypeNode::isBoolean() const {
  return getKind() == kind::TYPE_CONSTANT &&
    getConst<TypeConstant>() == BOOLEAN_TYPE;
}

bool TypeNode::isInteger() const {
  return getKind() == kind::TYPE_CONSTANT &&
    getConst<TypeConstant>() == INTEGER_TYPE;
}

bool TypeNode::isReal() const {
  return getKind() == kind::TYPE_CONSTANT
    && ( getConst<TypeConstant>() == REAL_TYPE ||
         getConst<TypeConstant>() == INTEGER_TYPE );
}

bool TypeNode::isArray() const {
  return getKind() == kind::ARRAY_TYPE;
}

TypeNode TypeNode::getArrayIndexType() const {
  Assert(isArray());
  return (*this)[0];
}

TypeNode TypeNode::getArrayConstituentType() const {
  Assert(isArray());
  return (*this)[1];
}

TypeNode TypeNode::getConstructorRangeType() const {
  Assert(isConstructor());
  return (*this)[getNumChildren()-1];
}

bool TypeNode::isFunction() const {
  return getKind() == kind::FUNCTION_TYPE;
}

bool TypeNode::isFunctionLike() const {
  return
    getKind() == kind::FUNCTION_TYPE ||
    getKind() == kind::CONSTRUCTOR_TYPE ||
    getKind() == kind::SELECTOR_TYPE ||
    getKind() == kind::TESTER_TYPE;
}

bool TypeNode::isPredicate() const {
  return isFunction() && getRangeType().isBoolean();
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

TypeNode TypeNode::getRangeType() const {
  if(isTester()) {
    return NodeManager::currentNM()->booleanType();
  }
  Assert(isFunction() || isConstructor() || isSelector());
  return (*this)[getNumChildren()-1];
}

/** Is this a tuple type? */
bool TypeNode::isTuple() const {
  return getKind() == kind::TUPLE_TYPE;
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

/** Is this a sort kind */
bool TypeNode::isSort() const {
  return getKind() == kind::SORT_TYPE && !hasAttribute(expr::SortArityAttr());
}

/** Is this a sort constructor kind */
bool TypeNode::isSortConstructor() const {
  return getKind() == kind::SORT_TYPE && hasAttribute(expr::SortArityAttr());
}

/** Is this a kind type (i.e., the type of a type)? */
bool TypeNode::isKind() const {
  return getKind() == kind::TYPE_CONSTANT &&
    getConst<TypeConstant>() == KIND_TYPE;
}

/** Is this a bit-vector type */
bool TypeNode::isBitVector() const {
  return getKind() == kind::BITVECTOR_TYPE;
}

/** Is this a datatype type */
bool TypeNode::isDatatype() const {
  return getKind() == kind::DATATYPE_TYPE;
}

/** Is this a parametric datatype type */
bool TypeNode::isParametricDatatype() const {
  return getKind() == kind::PARAMETRIC_DATATYPE;
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
  for(unsigned i = 0; i < n; ++i) {
    if(TypeNode::fromType(dt.getParameter(i)) == (*this)[n + 1]) {
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

/** Is this a constructor type */
bool TypeNode::isConstructor() const {
  return getKind() == kind::CONSTRUCTOR_TYPE;
}

/** Is this a selector type */
bool TypeNode::isSelector() const {
  return getKind() == kind::SELECTOR_TYPE;
}

/** Is this a tester type */
bool TypeNode::isTester() const {
  return getKind() == kind::TESTER_TYPE;
}

/** Is this a bit-vector type of size <code>size</code> */
bool TypeNode::isBitVector(unsigned size) const {
  return getKind() == kind::BITVECTOR_TYPE &&
    getConst<BitVectorSize>() == size;
}

/** Get the size of this bit-vector type */
unsigned TypeNode::getBitVectorSize() const {
  Assert(isBitVector());
  return getConst<BitVectorSize>();
}

}/* CVC4 namespace */
