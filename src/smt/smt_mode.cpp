/*********************                                                        */
/*! \file smt_mode.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumeration type for the mode of an SmtEngine.
 **/

#include "smt/smt_mode.h"

#include <iostream>

namespace CVC4 {
  
std::ostream& operator<<(std::ostream& out, SmtMode m)
{
  switch(m)
  {
    case SmtMode::START: return "START";
    case SmtMode::ASSERT: return "ASSERT";
  case SmtMode::SAT: return "SAT";
  case SmtMode::SAT_UNKNOWN: return "SAT_UNKNOWN";
  case SmtMode::UNSAT: return "UNSAT";
  case SmtMode::ABDUCT: return "ABDUCT";
  case SmtMode::INTERPOL: return "INTERPOL";
  default: out << "SmtMode!Unknown";
  }
  return out;
}

}  // namespace CVC4

