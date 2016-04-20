/*********************                                                        */
/*! \file arith_propagation_mode.cpp
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

#include "options/arith_propagation_mode.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, ArithPropagationMode mode) {
  switch(mode) {
  case NO_PROP:
    out << "NO_PROP";
    break;
  case UNATE_PROP:
    out << "UNATE_PROP";
    break;
  case BOUND_INFERENCE_PROP:
    out << "BOUND_INFERENCE_PROP";
    break;
  case BOTH_PROP:
    out << "BOTH_PROP";
    break;
  default:
    out << "ArithPropagationMode!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */
