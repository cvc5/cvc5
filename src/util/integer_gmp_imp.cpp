/*********************                                                        */
/*! \file integer_gmp_imp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A multi-precision rational constant.
 **
 ** A multi-precision rational constant.
 **/

#include "util/integer.h"

#include <cmath>
#include <sstream>
#include <string>

#include "cvc4autoconfig.h"

#include "base/cvc4_assert.h"
#include "util/rational.h"

#ifndef CVC4_GMP_IMP
#  error "This source should only ever be built if CVC4_GMP_IMP is on !"
#endif /* CVC4_GMP_IMP */


using namespace std;

namespace CVC4 {

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
                "Overflow detected in Integer::getSignedInt().");
  CheckArgument(d_value >= std::numeric_limits<int>::min(), this,
                "Overflow detected in Integer::getSignedInt().");
  CheckArgument(fitsSignedInt(), this,
                "Overflow detected in Integer::getSignedInt().");
  return (signed int) d_value.get_si();
}

unsigned int Integer::getUnsignedInt() const {
  // ensure there isn't overflow
  CheckArgument(d_value <= std::numeric_limits<unsigned int>::max(), this,
                "Overflow detected in Integer::getUnsignedInt()");
  CheckArgument(d_value >= std::numeric_limits<unsigned int>::min(), this,
                "Overflow detected in Integer::getUnsignedInt()");
  CheckArgument(fitsSignedInt(), this,
                "Overflow detected in Integer::getUnsignedInt()");
  return (unsigned int) d_value.get_ui();
}

bool Integer::fitsSignedLong() const {
  return d_value.fits_slong_p();
}

bool Integer::fitsUnsignedLong() const {
  return d_value.fits_ulong_p();
}

Integer Integer::oneExtend(uint32_t size, uint32_t amount) const {
  // check that the size is accurate
  DebugCheckArgument((*this) < Integer(1).multiplyByPow2(size), size);
  mpz_class res = d_value;

  for (unsigned i = size; i < size + amount; ++i) {
    mpz_setbit(res.get_mpz_t(), i);
  }

  return Integer(res);
}

Integer Integer::exactQuotient(const Integer& y) const {
  DebugCheckArgument(y.divides(*this), y);
  mpz_class q;
  mpz_divexact(q.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
  return Integer( q );
}

} /* namespace CVC4 */
