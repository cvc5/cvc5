/*********************                                                        */
/*! \file decision_mode.cpp
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

#include "options/decision_mode.h"

#include <iostream>

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, decision::DecisionMode mode) {
  switch(mode) {
  case decision::DECISION_STRATEGY_INTERNAL:
    out << "DECISION_STRATEGY_INTERNAL";
    break;
  case decision::DECISION_STRATEGY_JUSTIFICATION:
    out << "DECISION_STRATEGY_JUSTIFICATION";
    break;
  default:
    out << "DecisionMode:UNKNOWN![" << unsigned(mode) << "]";
  }

  return out;
}

}/* CVC4 namespace */
