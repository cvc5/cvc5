/*********************                                                        */
/** rational.cpp
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A multiprecision rational constant.
 **/

#include "util/rational.h"

using namespace CVC4;

std::ostream& CVC4::operator<<(std::ostream& os, const Rational& q){
  return os << q.toString();
}
