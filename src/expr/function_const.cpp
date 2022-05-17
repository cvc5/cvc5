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

using namespace std;

namespace cvc5::internal {

FunctionConstant::FunctionConstant(const TypeNode& type, const Node& avalue)
    : d_type(), d_avalue()
{
  // TODO: checks

  // Delay allocation until the checks above have been performed. If these
  // fail, the memory for d_type and d_avalue should not leak. The alternative
  // is catch, delete and re-throw.
  d_type.reset(new TypeNode(type));
  d_avalue.reset(new Node(avalue));
}

FunctionConstant::FunctionConstant(const FunctionConstant& other)
    : d_type(new TypeNode(other.getType())),
      d_avalue(new Node(other.getArrayValue()))
{
}

FunctionConstant::~FunctionConstant() {}
FunctionConstant& FunctionConstant::operator=(const FunctionConstant& other)
{
  (*d_type) = other.getType();
  (*d_avalue) = other.getArrayValue();
  return *this;
}

const TypeNode& FunctionConstant::getType() const { return *d_type; }

const Node& FunctionConstant::getArrayValue() const { return *d_avalue; }

bool FunctionConstant::operator==(const FunctionConstant& fc) const
{
  return getType() == fc.getType() && getArrayValue() == fc.getArrayValue();
}

bool FunctionConstant::operator!=(const FunctionConstant& fc) const
{
  return !(*this == fc);
}

bool FunctionConstant::operator<(const FunctionConstant& fc) const
{
  return (getType() < fc.getType())
         || (getType() == fc.getType() && getArrayValue() < fc.getArrayValue());
}

bool FunctionConstant::operator<=(const FunctionConstant& fc) const
{
  return (getType() < fc.getType())
         || (getType() == fc.getType()
             && getArrayValue() <= fc.getArrayValue());
}

bool FunctionConstant::operator>(const FunctionConstant& fc) const
{
  return !(*this <= fc);
}

bool FunctionConstant::operator>=(const FunctionConstant& fc) const
{
  return !(*this < fc);
}

std::ostream& operator<<(std::ostream& out, const FunctionConstant& fc)
{
  return out << "__function_constant(" << fc.getType() << ", "
             << fc.getArrayValue() << ')';
}

size_t FunctionConstantHashFunction::operator()(
    const FunctionConstant& fc) const
{
  return std::hash<TypeNode>()(fc.getType())
         * std::hash<Node>()(fc.getArrayValue());
}

}  // namespace cvc5::internal
