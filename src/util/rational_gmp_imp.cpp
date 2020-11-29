/*********************                                                        */
/*! \file rational_gmp_imp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Christopher L. Conway, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A multi-precision rational constant.
 **
 ** A multi-precision rational constant.
 **/
#include "util/rational.h"

#include <cmath>
#include <sstream>
#include <string>

#include "cvc4autoconfig.h"

#ifndef CVC4_GMP_IMP // Make sure this comes after cvc4autoconfig.h
#  error "This source should only ever be built if CVC4_GMP_IMP is on !"
#endif /* CVC4_GMP_IMP */

#include "base/check.h"

namespace CVC4 {

std::ostream& operator<<(std::ostream& os, const Rational& q){
  return os << q.toString();
}


/* Computes a rational given a decimal string. The rational
 * version of <code>xxx.yyy</code> is <code>xxxyyy/(10^3)</code>.
 */
Rational Rational::fromDecimal(const std::string& dec) {
  using std::string;
  // Find the decimal point, if there is one
  string::size_type i( dec.find(".") );
  if( i != string::npos ) {
    /* Erase the decimal point, so we have just the numerator. */
    Integer numerator( string(dec).erase(i,1) );

    /* Compute the denominator: 10 raise to the number of decimal places */
    int decPlaces = dec.size() - (i + 1);
    Integer denominator( Integer(10).pow(decPlaces) );

    return Rational( numerator, denominator );
  } else {
    /* No decimal point, assume it's just an integer. */
    return Rational( dec );
  }
}



/** Equivalent to calling (this->abs()).cmp(b.abs()) */
int Rational::absCmp(const Rational& q) const{
  const Rational& r = *this;
  int rsgn = r.sgn();
  int qsgn = q.sgn();
  if(rsgn == 0){
    return (qsgn == 0) ? 0 : -1;
  }else if(qsgn == 0){
    Assert(rsgn != 0);
    return 1;
  }else if((rsgn > 0) && (qsgn > 0)){
    return r.cmp(q);
  }else if((rsgn < 0) && (qsgn < 0)){
    // if r < q < 0, q.cmp(r) = +1, (r.abs()).cmp(q.abs()) = +1
    // if q < r < 0, q.cmp(r) = -1, (r.abs()).cmp(q.abs()) = -1
    // if q = r < 0, q.cmp(r) =  0, (r.abs()).cmp(q.abs()) =  0
    return q.cmp(r);
  }else if((rsgn < 0) && (qsgn > 0)){
    Rational rpos = -r;
    return rpos.cmp(q);
  }else {
    Assert(rsgn > 0 && (qsgn < 0));
    Rational qpos = -q;
    return r.cmp(qpos);
  }
}


/** Return an exact rational for a double d. */
Maybe<Rational> Rational::fromDouble(double d)
{
  using namespace std;
  if(isfinite(d)){
    Rational q;
    mpq_set_d(q.d_value.get_mpq_t(), d);
    return q;
  }
  return Maybe<Rational>();
}

} /* namespace CVC4 */
