/*********************                                                        */
/*! \file array_store_all.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of a constant array (an array in which the
 ** element is the same for all indices)
 **
 ** Representation of a constant array (an array in which the element is
 ** the same for all indices).
 **/

#include "expr/array_store_all.h"

#include <iostream>

using namespace std;

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const ArrayStoreAll& asa) {
  return out << "__array_store_all__(" << asa.getType() << ", " << asa.getExpr() << ')';
}

}/* CVC4 namespace */
