/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of an almost constant function
 */

#include "expr/function_const.h"

#include <iostream>

#include "base/check.h"
#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {

FunctionConstant::FunctionConstant(const Node& avalue)
    :  d_avalue(), d_type()
{
  Assert (avalue.isConst());
  d_avalue.reset(new Node(avalue));
  
  TypeNode tn = avalue.getType();
  Assert (tn.isArray());
  std::vector<TypeNode> argTypes;
  while (tn.isArray())
  {
    argTypes.push_back(tn.getArrayIndexType());
    tn = tn.getArrayConstituentType();
  }
  TypeNode type = NodeManager::currentNM()->mkFunctionType(argTypes, tn);
  d_type.reset(new TypeNode(type));
}

FunctionConstant::FunctionConstant(const FunctionConstant& other)
    : d_avalue(new Node(other.getArrayValue())), d_type(new TypeNode(other.getType()))
{
}

FunctionConstant::~FunctionConstant() {}
FunctionConstant& FunctionConstant::operator=(const FunctionConstant& other) {
  (*d_avalue) = other.getArrayValue();
  (*d_type) = other.getType();
  return *this;
}

const TypeNode& FunctionConstant::getType() const { 
  return *d_type;
}

const Node& FunctionConstant::getArrayValue() const { return *d_avalue; }

bool FunctionConstant::operator==(const FunctionConstant& fc) const
{
  return getArrayValue() == fc.getArrayValue();
}

bool FunctionConstant::operator!=(const FunctionConstant& fc) const
{
  return !(*this == fc);
}

bool FunctionConstant::operator<(const FunctionConstant& fc) const
{
  return getArrayValue() < fc.getArrayValue();
}

bool FunctionConstant::operator<=(const FunctionConstant& fc) const
{
  return getArrayValue() <= fc.getArrayValue();
}

bool FunctionConstant::operator>(const FunctionConstant& fc) const
{
  return !(*this <= fc);
}

bool FunctionConstant::operator>=(const FunctionConstant& fc) const
{
  return !(*this < fc);
}

//std::ostream& operator<<(std::ostream& out, const FunctionConstant& fc) {
//  return out << "__function_const"; //(" << fc.getArrayValue() << ')';
//}

size_t FunctionConstantHashFunction::operator()(const FunctionConstant& fc) const {
  return std::hash<Node>()(fc.getArrayValue());
}

}  // namespace cvc5::internal
