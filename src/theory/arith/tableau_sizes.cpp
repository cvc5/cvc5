/*********************                                                        */
/*! \file tableau_sizes.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "base/output.h"
#include "theory/arith/tableau_sizes.h"
#include "theory/arith/tableau.h"

namespace CVC4 {
namespace theory {
namespace arith {

uint32_t TableauSizes::getRowLength(ArithVar b) const {
  return d_tab->basicRowLength(b);
}

uint32_t TableauSizes::getColumnLength(ArithVar x) const {
  return d_tab->getColLength(x);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
