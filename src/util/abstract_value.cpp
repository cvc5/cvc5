/*********************                                                        */
/*! \file abstract_value.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
