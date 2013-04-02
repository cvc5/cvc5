/*********************                                                        */
/*! \file abstract_value.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of abstract values
 **
 ** Representation of abstract values.
 **/

#include "util/abstract_value.h"
#include <iostream>
#include <sstream>
#include <string>

using namespace std;

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const AbstractValue& val) {
  return out << "@" << val.getIndex();
}

}/* CVC4 namespace */
