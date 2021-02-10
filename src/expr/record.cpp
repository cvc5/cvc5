/*********************                                                        */
/*! \file record.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class representing a record definition
 **
 ** A class representing a record definition.
 **/

#include "expr/record.h"

#include "base/check.h"
#include "base/output.h"


namespace CVC4 {

std::ostream& operator<<(std::ostream& out, const RecordUpdate& t) {
  return out << "[" << t.getField() << "]";
}

}/* CVC4 namespace */
