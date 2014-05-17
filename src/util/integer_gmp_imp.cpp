/*********************                                                        */
/*! \file integer_gmp_imp.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: Morgan Deters, Christopher L. Conway
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A multi-precision rational constant.
 **
 ** A multi-precision rational constant.
 **/

#include "cvc4autoconfig.h"
#include "util/rational.h"
#include <string>
#include <sstream>
#include <cmath>

#ifndef CVC4_GMP_IMP
#  error "This source should only ever be built if CVC4_GMP_IMP is on !"
#endif /* CVC4_GMP_IMP */

using namespace std;
using namespace CVC4;



Integer::Integer(const char* s, unsigned base)
  : d_value(s, base)
{}

Integer::Integer(const std::string& s, unsigned base)
  : d_value(s, base)
{}


bool Integer::fitsSignedInt() const {
  return d_value.fits_sint_p();
}

bool Integer::fitsUnsignedInt() const {
  return d_value.fits_uint_p();
}

signed int Integer::getSignedInt() const {
  // ensure there isn't overflow
  CheckArgument(d_value <= std::numeric_limits<int>::max(), this,
                "Overflow detected in Integer::getSignedInt()");
  CheckArgument(d_value >= std::numeric_limits<int>::min(), this,
                "Overflow detected in Integer::getSignedInt()");
  CheckArgument(fitsSignedInt(), this, "Overflow detected in Integer::getSignedInt()");
  return (signed int) d_value.get_si();
}

unsigned int Integer::getUnsignedInt() const {
  // ensure there isn't overflow
  CheckArgument(d_value <= std::numeric_limits<unsigned int>::max(), this,
                "Overflow detected in Integer::getUnsignedInt()");
  CheckArgument(d_value >= std::numeric_limits<unsigned int>::min(), this,
                "Overflow detected in Integer::getUnsignedInt()");
  CheckArgument(fitsSignedInt(), this, "Overflow detected in Integer::getUnsignedInt()");
  return (unsigned int) d_value.get_ui();
}
