/*********************                                                        */
/*! \file decision_mode.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2014  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "options/decision_mode.h"

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
