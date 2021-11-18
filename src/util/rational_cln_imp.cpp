/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Christopher L. Conway, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A multi-precision rational constant.
 */
#include <sstream>
#include <string>

#include "base/cvc5config.h"
#include "util/rational.h"

#ifndef CVC5_CLN_IMP
#error "This source should only ever be built if CVC5_CLN_IMP is on !"
#endif /* CVC5_CLN_IMP */

#include "base/check.h"

using namespace std;

namespace cvc5 {

/* Computes a rational given a decimal string. The rational
 * version of <code>xxx.yyy</code> is <code>xxxyyy/(10^3)</code>.
 */
Rational Rational::fromDecimal(const std::string& dec) {
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

Rational::Rational(const char* s, unsigned base)
{
  try
  {
    const char* p = strchr(s, '/');
    /* read_rational() does not support the case where the denominator is
     * negative.  In this case we split the string into numerator and
     * denominator and build rational out of two Integers. */
    if (p && p != s && p[1] == '-')
    {
      size_t len = strlen(s);
      size_t pos = p - s;
      char str[len + 1];
      strncpy(str, s, len);
      str[len] = 0;
      str[pos] = 0;
      Integer num = Integer(str, base);
      Integer den = Integer(str + pos + 1, base);
      d_value = num.get_cl_I() / den.get_cl_I();
    }
    else
    {
      cln::cl_read_flags flags;
      flags.syntax = cln::syntax_rational;
      flags.lsyntax = cln::lsyntax_standard;
      flags.rational_base = base;
      d_value = read_rational(flags, s, NULL, NULL);
    }
  }
  catch (...)
  {
    std::stringstream ss;
    ss << "Rational() failed to parse value \"" << s << "\" in base=" << base;
    throw std::invalid_argument(ss.str());
  }
}

Rational::Rational(const std::string& s, unsigned base)
    : Rational(s.c_str(), base)
{
}

int Rational::sgn() const
{
  if (cln::zerop(d_value))
  {
    return 0;
  }
  else if (cln::minusp(d_value))
  {
    return -1;
  }
  else
  {
    Assert(cln::plusp(d_value));
    return 1;
  }
}

std::ostream& operator<<(std::ostream& os, const Rational& q){
  return os << q.toString();
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

std::optional<Rational> Rational::fromDouble(double d)
{
  try{
    cln::cl_DF fromD = d;
    Rational q;
    q.d_value = cln::rationalize(fromD);
    return q;
  }catch(cln::floating_point_underflow_exception& fpue){
    return std::optional<Rational>();
  }catch(cln::floating_point_nan_exception& fpne){
    return std::optional<Rational>();
  }catch(cln::floating_point_overflow_exception& fpoe){
    return std::optional<Rational>();
  }
}

}  // namespace cvc5
