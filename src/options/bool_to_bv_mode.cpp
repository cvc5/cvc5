/*********************                                                        */
/*! \file bool_to_bv_mode.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Makai Mann
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** [[ Add lengthier description here ]]

 ** \todo document this file

**/

#include "options/bool_to_bv_mode.h"

#include <iostream>


namespace CVC4
{
  std::ostream& operator<<(std::ostream& out, preprocessing::passes::BoolToBVMode mode) {
    switch(mode) {
    case preprocessing::passes::BOOL_TO_BV_OFF:
      out << "BOOL_TO_BV_OFF";
      break;
    case preprocessing::passes::BOOL_TO_BV_ITE:
      out << "BOOL_TO_BV_ITE";
      break;
    case preprocessing::passes::BOOL_TO_BV_ALL:
      out << "BOOL_TO_BV_ALL";
      break;
    default:
      out << "BoolToBVMode:UNKNOWN![" << unsigned(mode) << "]";
    }

    return out;
  }
} // namespace CVC4
