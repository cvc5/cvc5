/*********************                                                        */
/*! \file incomplete_id.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of incompleteness enumeration.
 **/

#include "theory/incomplete_id.h"

#include <iostream>

namespace cvc5 {
namespace theory {

const char* toString(IncompleteId i)
{
  switch (i)
  {
    case IncompleteId::UNKNOWN: return "UNKNOWN";
    default: return "?IncompleteId?";
  }
}

std::ostream& operator<<(std::ostream& out, IncompleteId i)
{
  out << toString(i);
  return out;
}

}  // namespace theory
}  // namespace cvc5
