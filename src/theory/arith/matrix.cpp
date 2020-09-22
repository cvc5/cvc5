/*********************                                                        */
/*! \file matrix.cpp
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


#include "theory/arith/matrix.h"

using namespace std;
namespace CVC4 {
namespace theory {
namespace arith {

void NoEffectCCCB::update(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn) {}
void NoEffectCCCB::multiplyRow(RowIndex ridx, int sgn){}
bool NoEffectCCCB::canUseRow(RowIndex ridx) const { return false; }

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
