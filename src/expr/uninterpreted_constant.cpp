/*********************                                                        */
/*! \file uninterpreted_constant.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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

using namespace std;

namespace CVC4 {

UninterpretedConstant::UninterpretedConstant(Type type, Integer index)
    : d_type(type), d_index(index)
{
  //PrettyCheckArgument(type.isSort(), type, "uninterpreted constants can only be created for uninterpreted sorts, not `%s'", type.toString().c_str());
  PrettyCheckArgument(index >= 0, index, "index >= 0 required for uninterpreted constant index, not `%s'", index.toString().c_str());
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

}/* CVC4 namespace */
