/*********************                                                        */
/*! \file boolean_term_conversion_mode.cpp
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
#include "options/boolean_term_conversion_mode.h"

#include <iostream>

namespace CVC4 {

std::ostream& operator<<(std::ostream& out, theory::booleans::BooleanTermConversionMode mode) {
  switch(mode) {
  case theory::booleans::BOOLEAN_TERM_CONVERT_TO_BITVECTORS:
    out << "BOOLEAN_TERM_CONVERT_TO_BITVECTORS";
    break;
  case theory::booleans::BOOLEAN_TERM_CONVERT_TO_DATATYPES:
    out << "BOOLEAN_TERM_CONVERT_TO_DATATYPES";
    break;
  case theory::booleans::BOOLEAN_TERM_CONVERT_NATIVE:
    out << "BOOLEAN_TERM_CONVERT_NATIVE";
    break;
  default:
    out << "BooleanTermConversionMode!UNKNOWN";
  }

  return out;
}

}/* CVC4 namespace */
