/*********************                                                        */
/*! \file uninterpreted_constant.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of constants of uninterpreted sorts
 **
 ** Representation of constants of uninterpreted sorts.
 **/

#include "expr/uninterpreted_constant.h"

#include <algorithm>
#include <iostream>
#include <sstream>
#include <string>

#include "base/check.h"
#include "expr/type_node.h"

using namespace std;

namespace CVC4 {

UninterpretedConstant::UninterpretedConstant(const TypeNode& type,
                                             Integer index)
    : d_type(new TypeNode(type)), d_index(index)
{
  //PrettyCheckArgument(type.isSort(), type, "uninterpreted constants can only be created for uninterpreted sorts, not `%s'", type.toString().c_str());
  PrettyCheckArgument(index >= 0, index, "index >= 0 required for uninterpreted constant index, not `%s'", index.toString().c_str());
}

UninterpretedConstant::~UninterpretedConstant() {}

UninterpretedConstant::UninterpretedConstant(const UninterpretedConstant& other)
    : d_type(new TypeNode(other.getType())), d_index(other.getIndex())
{
}

const TypeNode& UninterpretedConstant::getType() const { return *d_type; }
const Integer& UninterpretedConstant::getIndex() const { return d_index; }
bool UninterpretedConstant::operator==(const UninterpretedConstant& uc) const
{
  return getType() == uc.getType() && d_index == uc.d_index;
}
bool UninterpretedConstant::operator!=(const UninterpretedConstant& uc) const
{
  return !(*this == uc);
}

bool UninterpretedConstant::operator<(const UninterpretedConstant& uc) const
{
  return getType() < uc.getType()
         || (getType() == uc.getType() && d_index < uc.d_index);
}
bool UninterpretedConstant::operator<=(const UninterpretedConstant& uc) const
{
  return getType() < uc.getType()
         || (getType() == uc.getType() && d_index <= uc.d_index);
}
bool UninterpretedConstant::operator>(const UninterpretedConstant& uc) const
{
  return !(*this <= uc);
}
bool UninterpretedConstant::operator>=(const UninterpretedConstant& uc) const
{
  return !(*this < uc);
}

std::ostream& operator<<(std::ostream& out, const UninterpretedConstant& uc) {
  std::stringstream ss;
  ss << uc.getType();
  std::string st(ss.str());
  // must remove delimiting quotes from the name of the type
  // this prevents us from printing symbols like |@uc_|T|_n|
  std::string q("|");
  size_t pos;
  while ((pos = st.find(q)) != std::string::npos)
  {
    st.replace(pos, 1, "");
  }
  return out << "uc_" << st.c_str() << "_" << uc.getIndex();
}

size_t UninterpretedConstantHashFunction::operator()(
    const UninterpretedConstant& uc) const
{
  return TypeNodeHashFunction()(uc.getType())
         * IntegerHashFunction()(uc.getIndex());
}

}/* CVC4 namespace */
