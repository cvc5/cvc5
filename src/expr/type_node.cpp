/*********************                                                        */
/** node.cpp
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Reference-counted encapsulation of a pointer to node information.
 **/

#include "expr/type_node.h"

namespace CVC4 {

TypeNode TypeNode::s_null(&expr::NodeValue::s_null);

bool TypeNode::isBoolean() const {
  return getKind() == kind::TYPE_CONSTANT && getConst<TypeConstant>() == BOOLEAN_TYPE;
}

bool TypeNode::isInteger() const {
  return getKind() == kind::TYPE_CONSTANT && getConst<TypeConstant>() == INTEGER_TYPE;
}

bool TypeNode::isReal() const {
  return getKind() == kind::TYPE_CONSTANT && getConst<TypeConstant>() == REAL_TYPE;
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

std::vector<TypeNode> TypeNode::getArgTypes() const {
  Assert(isFunction());
  std::vector<TypeNode> args;
  for (unsigned i = 0, i_end = getNumChildren() - 1; i < i_end; ++ i) {
    args.push_back((*this)[i]);
  }
  return args;
}

TypeNode TypeNode::getRangeType() const {
  Assert(isFunction());
  return (*this)[getNumChildren()-1];
}


/** Is this a sort kind */
bool TypeNode::isSort() const {
  return getKind() == kind::VARIABLE;
}

/** Is this a kind type (i.e., the type of a type)? */
bool TypeNode::isKind() const {
  return getKind() == kind::TYPE_CONSTANT && getConst<TypeConstant>() == KIND_TYPE;
}

}/* CVC4 namespace */
