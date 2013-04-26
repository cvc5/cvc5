/*********************                                                        */
/*! \file matrix.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
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


#include "theory/arith/matrix.h"

using namespace std;
namespace CVC4 {
namespace theory {
namespace arith {

void NoEffectCCCB::update(RowIndex ridx, ArithVar nb, int oldSgn, int currSgn) {}
void NoEffectCCCB::swap(ArithVar basic, ArithVar nb, int nbSgn){}
bool NoEffectCCCB::canUseRow(RowIndex ridx) const { return false; }

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
