/*********************                                                        */
/*! \file arith_heuristic_pivot_rule.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "options/arith_heuristic_pivot_rule.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, ErrorSelectionRule rule) {
  switch(rule) {
  case MINIMUM_AMOUNT:
    out << "MINIMUM_AMOUNT";
    break;
  case VAR_ORDER:
    out << "VAR_ORDER";
    break;
  case MAXIMUM_AMOUNT:
    out << "MAXIMUM_AMOUNT";
    break;
  default:
    out << "ArithHeuristicPivotRule!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */
