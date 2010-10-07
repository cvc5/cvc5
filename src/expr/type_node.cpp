/*********************                                                        */
/*! \file type_node.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

using namespace std;

namespace CVC4 {

TypeNode TypeNode::s_null( &expr::NodeValue::s_null );

TypeNode TypeNode::substitute(const TypeNode& type,
                              const TypeNode& replacement) const {
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
  return nb.constructTypeNode();
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

/** Is this a function type? */
bool TypeNode::isFunction() const {
  return getKind() == kind::FUNCTION_TYPE;
}

/** Is this a predicate type? NOTE: all predicate types are also
    function types. */
bool TypeNode::isPredicate() const {
  return isFunction() && getRangeType().isBoolean();
}

vector<TypeNode> TypeNode::getArgTypes() const {
  Assert(isFunction());
  vector<TypeNode> args;
  for(unsigned i = 0, i_end = getNumChildren() - 1; i < i_end; ++i) {
    args.push_back((*this)[i]);
  }
  return args;
}

TypeNode TypeNode::getRangeType() const {
  Assert(isFunction());
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
