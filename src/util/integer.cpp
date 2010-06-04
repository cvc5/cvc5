/*********************                                                        */
/*! \file integer.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A multiprecision rational constant.
 **
 ** A multiprecision rational constant.
 ** This stores the rational as a pair of multiprecision integers,
 ** one for the numerator and one for the denominator.
 ** The number is always stored so that the gcd of the numerator and denominator
 ** is 1.  (This is referred to as referred to as canonical form in GMP's
 ** literature.) A consquence is that that the numerator and denominator may be
 ** different than the values used to construct the Rational.
 **/

#include "util/integer.h"

using namespace CVC4;

std::ostream& CVC4::operator<<(std::ostream& os, const Integer& n) {
  return os << n.toString();
}
