/*********************                                                        */
/*! \file uninterpreted_constant.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Paul Meng
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of constants of uninterpreted sorts
 **
 ** Representation of constants of uninterpreted sorts.
 **/

#include "expr/uninterpreted_constant.h"

#include <iostream>
#include <sstream>
#include <string>

#include "base/cvc4_assert.h"

using namespace std;

namespace CVC4 {

UninterpretedConstant::UninterpretedConstant(Type type, Integer index)
    : d_type(type), d_index(index)
{
  //PrettyCheckArgument(type.isSort(), type, "uninterpreted constants can only be created for uninterpreted sorts, not `%s'", type.toString().c_str());
  PrettyCheckArgument(index >= 0, index, "index >= 0 required for uninterpreted constant index, not `%s'", index.toString().c_str());
}

std::ostream& operator<<(std::ostream& out, const UninterpretedConstant& uc) {
  stringstream ss;
  ss << uc.getType();
  string t = ss.str();
  size_t i = 0;
  // replace everything that isn't in [a-zA-Z0-9_] with an _
  while((i = t.find_first_not_of("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ1234567890_", i)) != string::npos) {
    t.replace(i, 1, 1, '_');
  }
  return out << "uc_" << t << '_' << uc.getIndex();
}

}/* CVC4 namespace */
