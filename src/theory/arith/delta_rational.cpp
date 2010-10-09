/*********************                                                        */
/*! \file delta_rational.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "theory/arith/delta_rational.h"

using namespace std;
using namespace CVC4;

std::ostream& CVC4::operator<<(std::ostream& os, const DeltaRational& dq){
  return os << "(" << dq.getNoninfinitesimalPart()
            << "," << dq.getInfinitesimalPart() << ")";
}


std::string DeltaRational::toString() const {
  return "(" + getNoninfinitesimalPart().toString() + "," +
    getInfinitesimalPart().toString() + ")";
}
