/*********************                                                        */
/*! \file inst_when_mode.cpp
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
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <iostream>
#include "theory/quantifiers/inst_when_mode.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, theory::quantifiers::InstWhenMode mode) {
  switch(mode) {
  case theory::quantifiers::INST_WHEN_PRE_FULL:
    out << "INST_WHEN_PRE_FULL";
    break;
  case theory::quantifiers::INST_WHEN_FULL:
    out << "INST_WHEN_FULL";
    break;
  case theory::quantifiers::INST_WHEN_FULL_LAST_CALL:
    out << "INST_WHEN_FULL_LAST_CALL";
    break;
  case theory::quantifiers::INST_WHEN_LAST_CALL:
    out << "INST_WHEN_LAST_CALL";
    break;
  default:
    out << "InstWhenMode!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */

