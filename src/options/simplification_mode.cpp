/*********************                                                        */
/*! \file simplification_mode.cpp
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

#include "options/simplification_mode.h"

#include <iostream>

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, SimplificationMode mode) {
  switch(mode) {
  case SIMPLIFICATION_MODE_BATCH:
    out << "SIMPLIFICATION_MODE_BATCH";
    break;
  case SIMPLIFICATION_MODE_NONE:
    out << "SIMPLIFICATION_MODE_NONE";
    break;
  default:
    out << "SimplificationMode:UNKNOWN![" << unsigned(mode) << "]";
  }

  return out;
}

}/* CVC4 namespace */
