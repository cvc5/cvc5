/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Function array constant, which is an almost constant function
 */

#include "expr/function_array_const.h"

#include <iostream>

#include "base/check.h"
#include "expr/node.h"
#include "expr/type_node.h"

using namespace std;

namespace cvc5::internal {

bool isFunctionCompatibleWithArray(const TypeNode& ftype, const TypeNode& atype)
{
  if (!ftype.isFunction())
  {
    return false;
  }
  std::vector<TypeNode> argTypes = ftype.getArgTypes();
  TypeNode atc = atype;
  for (size_t i = 0, nargs = argTypes.size(); i < nargs; i++)
  {
    if (!atc.isArray() || argTypes[i] != atc.getArrayIndexType())
    {
      return false;
    }
    atc = atc.getArrayConstituentType();
  }
  return true;
}

FunctionArrayConst::FunctionArrayConst(const TypeNode& type, const Node& avalue)
    : d_type(), d_avalue()
{
  Assert(avalue.isConst());
  Assert(avalue.getType().isArray());
  Assert(isFunctionCompatibleWithArray(type, avalue.getType()));

  d_type.reset(new TypeNode(type));
  d_avalue.reset(new Node(avalue));
}

FunctionArrayConst::FunctionArrayConst(const FunctionArrayConst& other)
    : d_type(new TypeNode(other.getType())),
      d_avalue(new Node(other.getArrayValue()))
{
}

FunctionArrayConst::~FunctionArrayConst() {}
FunctionArrayConst& FunctionArrayConst::operator=(
    const FunctionArrayConst& other)
{
  (*d_type) = other.getType();
  (*d_avalue) = other.getArrayValue();
  return *this;
}

const TypeNode& FunctionArrayConst::getType() const { return *d_type; }

const Node& FunctionArrayConst::getArrayValue() const { return *d_avalue; }

bool FunctionArrayConst::operator==(const FunctionArrayConst& fc) const
{
  return getType() == fc.getType() && getArrayValue() == fc.getArrayValue();
}

bool FunctionArrayConst::operator!=(const FunctionArrayConst& fc) const
{
  return !(*this == fc);
}

bool FunctionArrayConst::operator<(const FunctionArrayConst& fc) const
{
  return (getType() < fc.getType())
         || (getType() == fc.getType() && getArrayValue() < fc.getArrayValue());
}

bool FunctionArrayConst::operator<=(const FunctionArrayConst& fc) const
{
  return (getType() < fc.getType())
         || (getType() == fc.getType()
             && getArrayValue() <= fc.getArrayValue());
}

bool FunctionArrayConst::operator>(const FunctionArrayConst& fc) const
{
  return !(*this <= fc);
}

bool FunctionArrayConst::operator>=(const FunctionArrayConst& fc) const
{
  return !(*this < fc);
}

std::ostream& operator<<(std::ostream& out, const FunctionArrayConst& fc)
{
  return out << "__function_constant(" << fc.getType() << ", "
             << fc.getArrayValue() << ')';
}

size_t FunctionArrayConstHashFunction::operator()(
    const FunctionArrayConst& fc) const
{
  return std::hash<TypeNode>()(fc.getType())
         * std::hash<Node>()(fc.getArrayValue());
}

}  // namespace cvc5::internal
