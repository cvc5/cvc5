/*********************                                                        */
/*! \file pseudoboolean.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute &of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A pseudoboolean constant
 **
 ** A pseudoboolean constant.
 **/

#include "util/pseudoboolean.h"

namespace CVC4 {

Pseudoboolean::Pseudoboolean(bool b) :
  d_value(b) {
}

Pseudoboolean::Pseudoboolean(int i) {
  CheckArgument(i == 0 || i == 1, i);
  d_value = (i == 1);
}

Pseudoboolean::Pseudoboolean(const Integer& i) {
  CheckArgument(i == 0 || i == 1, i);
  d_value = (i == 1);
}

Pseudoboolean::operator bool() const {
  return d_value;
}

Pseudoboolean::operator int() const {
  return d_value ? 1 : 0;
}

Pseudoboolean::operator Integer() const {
  return d_value ? 1 : 0;
}

}/* CVC4 namespace */
