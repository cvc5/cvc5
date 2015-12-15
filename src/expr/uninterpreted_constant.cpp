/*********************                                                        */
/*! \file uninterpreted_constant.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of constants of uninterpreted sorts
 **
 ** Representation of constants of uninterpreted sorts.
 **/

#include "expr/uninterpreted_constant.h"

#include <iostream>
#include <sstream>
#include <string>

using namespace std;

namespace CVC4 {

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
