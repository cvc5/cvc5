/*********************                                                        */
/*! \file rewrites.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mudathir Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of inference information utility.
 **/

#include "theory/bags/rewrites.h"

#include <iostream>

namespace CVC4 {
namespace theory {
namespace bags {

const char* toString(Rewrite r)
{
  switch (r)
  {
    // case Rewrite::CTN_COMPONENT: return "CTN_COMPONENT";
    default: return "?";
  }
}

std::ostream& operator<<(std::ostream& out, Rewrite r)
{
  out << toString(r);
  return out;
}

}  // namespace bags
}  // namespace theory
}  // namespace CVC4
