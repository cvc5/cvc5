/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Representation of bound variables in codatatype values
 */

#include "expr/codatatype_bound_variable.h"

#include <algorithm>
#include <iostream>
#include <sstream>
#include <string>

#include "base/check.h"
#include "expr/type_node.h"

using namespace std;

namespace cvc5::internal {

CodatatypeBoundVariable::CodatatypeBoundVariable(const TypeNode& type,
                                                 Integer index)
    : d_type(new TypeNode(type)), d_index(index)
{
  Assert(type.isCodatatype())
      << "codatatype bound variables can only be created for "
         "codatatype sorts, not `"
      << type.toString().c_str() << "'";
  Assert(index >= 0)
      << "index >= 0 required for codatatype bound variable index, not `"
      << index.toString().c_str() << "'";
}

CodatatypeBoundVariable::~CodatatypeBoundVariable() {}

CodatatypeBoundVariable::CodatatypeBoundVariable(
    const CodatatypeBoundVariable& other)
    : d_type(new TypeNode(other.getType())), d_index(other.getIndex())
{
}

const TypeNode& CodatatypeBoundVariable::getType() const { return *d_type; }
const Integer& CodatatypeBoundVariable::getIndex() const { return d_index; }
bool CodatatypeBoundVariable::operator==(
    const CodatatypeBoundVariable& cbv) const
{
  return getType() == cbv.getType() && d_index == cbv.d_index;
}
bool CodatatypeBoundVariable::operator!=(
    const CodatatypeBoundVariable& cbv) const
{
  return !(*this == cbv);
}

bool CodatatypeBoundVariable::operator<(
    const CodatatypeBoundVariable& cbv) const
{
  return getType() < cbv.getType()
         || (getType() == cbv.getType() && d_index < cbv.d_index);
}
bool CodatatypeBoundVariable::operator<=(
    const CodatatypeBoundVariable& cbv) const
{
  return getType() < cbv.getType()
         || (getType() == cbv.getType() && d_index <= cbv.d_index);
}
bool CodatatypeBoundVariable::operator>(
    const CodatatypeBoundVariable& cbv) const
{
  return !(*this <= cbv);
}
bool CodatatypeBoundVariable::operator>=(
    const CodatatypeBoundVariable& cbv) const
{
  return !(*this < cbv);
}

std::ostream& operator<<(std::ostream& out, const CodatatypeBoundVariable& cbv)
{
  std::stringstream ss;
  ss << cbv.getType();
  std::string st(ss.str());
  // must remove delimiting quotes from the name of the type
  // this prevents us from printing symbols like |@cbv_|T|_n|
  std::string q("|");
  size_t pos;
  while ((pos = st.find(q)) != std::string::npos)
  {
    st.replace(pos, 1, "");
  }
  return out << "cbv_" << st.c_str() << "_" << cbv.getIndex();
}

size_t CodatatypeBoundVariableHashFunction::operator()(
    const CodatatypeBoundVariable& cbv) const
{
  return std::hash<TypeNode>()(cbv.getType())
         * IntegerHashFunction()(cbv.getIndex());
}

}  // namespace cvc5::internal
