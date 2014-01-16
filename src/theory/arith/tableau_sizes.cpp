/*********************                                                        */
/*! \file tableau_sizes.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

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
