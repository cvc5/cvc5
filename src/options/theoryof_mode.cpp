/*********************                                                        */
/*! \file theoryof_mode.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
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


#include "options/theoryof_mode.h"

#include <ostream>
#include "base/cvc4_assert.h"

namespace CVC4 {
namespace theory {

std::ostream& operator<<(std::ostream& out, TheoryOfMode m) throw() {
  switch(m) {
  case THEORY_OF_TYPE_BASED: return out << "THEORY_OF_TYPE_BASED";
  case THEORY_OF_TERM_BASED: return out << "THEORY_OF_TERM_BASED";
  default: return out << "TheoryOfMode!UNKNOWN";
  }

  Unreachable();
}

}/* CVC4::theory namespace */
}/* CVC4 namespace */
