/*********************                                                        */
/*! \file integer_cln_imp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Aina Niemetz, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "util/integer.h"

#include <sstream>
#include <string>

#include "cvc4autoconfig.h"


#ifndef CVC4_CLN_IMP
#  error "This source should only ever be built if CVC4_CLN_IMP is on !"
#endif /* CVC4_CLN_IMP */

#include "base/check.h"

using namespace std;

namespace CVC4 {

signed int Integer::s_fastSignedIntMin = -(1<<29);
signed int Integer::s_fastSignedIntMax = (1<<29)-1;
signed long Integer::s_slowSignedIntMin = (signed long) std::numeric_limits<signed int>::min();
signed long Integer::s_slowSignedIntMax =  (signed long) std::numeric_limits<signed int>::max();

unsigned int Integer::s_fastUnsignedIntMax = (1<<29)-1;
unsigned long Integer::s_slowUnsignedIntMax =  (unsigned long) std::numeric_limits<unsigned int>::max();

unsigned long Integer::s_signedLongMin = std::numeric_limits<signed long>::min();
unsigned long Integer::s_signedLongMax = std::numeric_limits<signed long>::max();
unsigned long Integer::s_unsignedLongMax = std::numeric_limits<unsigned long>::max();

Integer Integer::oneExtend(uint32_t size, uint32_t amount) const {
  DebugCheckArgument((*this) < Integer(1).multiplyByPow2(size), size);
  cln::cl_byte range(amount, size);
  cln::cl_I allones = (cln::cl_I(1) << (size + amount))- 1; // 2^size - 1
  Integer temp(allones);

  return Integer(cln::deposit_field(allones, d_value, range));
}


Integer Integer::exactQuotient(const Integer& y) const {
  DebugCheckArgument(y.divides(*this), y);
  return Integer( cln::exquo(d_value, y.d_value) );
}

void Integer::parseInt(const std::string& s, unsigned base)
{
  cln::cl_read_flags flags;
  flags.syntax = cln::syntax_integer;
  flags.lsyntax = cln::lsyntax_standard;
  flags.rational_base = base;
  if(base == 0) {
    // infer base in a manner consistent with GMP
    if(s[0] == '0') {
      flags.lsyntax = cln::lsyntax_commonlisp;
      std::string st = s;
      if(s[1] == 'X' || s[1] == 'x') {
        st.replace(0, 2, "#x");
      } else if(s[1] == 'B' || s[1] == 'b') {
        st.replace(0, 2, "#b");
      } else {
        st.replace(0, 1, "#o");
      }
      readInt(flags, st, base);
      return;
    } else {
      flags.rational_base = 10;
    }
  }
  readInt(flags, s, base);
}

void Integer::readInt(const cln::cl_read_flags& flags,
                      const std::string& s,
                      unsigned base)
{
  try {
    // Removing leading zeroes, CLN has a bug for these inputs up to and
    // including CLN v1.3.2.
    // See http://www.ginac.de/CLN/cln.git/?a=commit;h=4a477b0cc3dd7fbfb23b25090ff8c8869c8fa21a for details.
    size_t pos = s.find_first_not_of('0');
    if(pos == std::string::npos) {
      d_value = read_integer(flags, "0", NULL, NULL);
    } else {
      const char* cstr = s.c_str();
      const char* start = cstr + pos;
      const char* end = cstr + s.length();
      d_value = read_integer(flags, start, end, NULL);
    }
  } catch(...) {
    std::stringstream ss;
    ss << "Integer() failed to parse value \"" << s << "\" in base " << base;
    throw std::invalid_argument(ss.str());
  }
}

bool Integer::fitsSignedInt() const {
  // http://www.ginac.de/CLN/cln.html#Conversions
  // TODO improve performance
  Assert(s_slowSignedIntMin <= s_fastSignedIntMin);
  Assert(s_fastSignedIntMin <= s_fastSignedIntMax);
  Assert(s_fastSignedIntMax <= s_slowSignedIntMax);

  return (d_value <= s_fastSignedIntMax || d_value <= s_slowSignedIntMax) &&
    (d_value >= s_fastSignedIntMin || d_value >= s_slowSignedIntMax);
}

bool Integer::fitsUnsignedInt() const {
  // TODO improve performance
  Assert(s_fastUnsignedIntMax <= s_slowUnsignedIntMax);
  return sgn() >= 0 &&
    (d_value <= s_fastUnsignedIntMax || d_value <= s_slowUnsignedIntMax);
}

signed int Integer::getSignedInt() const {
  // ensure there isn't overflow
  CheckArgument(fitsSignedInt(), this, "Overflow detected in Integer::getSignedInt()");
  return cln::cl_I_to_int(d_value);
}

unsigned int Integer::getUnsignedInt() const {
  // ensure there isn't overflow
  CheckArgument(fitsUnsignedInt(), this, "Overflow detected in Integer::getUnsignedInt()");
  return cln::cl_I_to_uint(d_value);
}

bool Integer::fitsSignedLong() const {
  return d_value <= s_signedLongMax && d_value >= s_signedLongMin;
}

bool Integer::fitsUnsignedLong() const {
  return sgn() >= 0 && d_value <= s_unsignedLongMax;
}

Integer Integer::pow(unsigned long int exp) const {
  if (exp == 0) {
    return Integer(1);
  } else {
    Assert(exp > 0);
    cln::cl_I result = cln::expt_pos(d_value, exp);
    return Integer(result);
  }
}

Integer Integer::modAdd(const Integer& y, const Integer& m) const
{
  cln::cl_modint_ring ry = cln::find_modint_ring(m.d_value);
  cln::cl_MI xm = ry->canonhom(d_value);
  cln::cl_MI ym = ry->canonhom(y.d_value);
  cln::cl_MI res = xm + ym;
  return Integer(ry->retract(res));
}

Integer Integer::modMultiply(const Integer& y, const Integer& m) const
{
  cln::cl_modint_ring ry = cln::find_modint_ring(m.d_value);
  cln::cl_MI xm = ry->canonhom(d_value);
  cln::cl_MI ym = ry->canonhom(y.d_value);
  cln::cl_MI res = xm * ym;
  return Integer(ry->retract(res));
}

Integer Integer::modInverse(const Integer& m) const
{
  PrettyCheckArgument(m > 0, m, "m must be greater than zero");
  cln::cl_modint_ring ry = cln::find_modint_ring(m.d_value);
  cln::cl_MI xm = ry->canonhom(d_value);
  /* normalize to modulo m for coprime check */
  cln::cl_I x = ry->retract(xm);
  if (x == 0 || cln::gcd(x, m.d_value) != 1)
  {
    return Integer(-1);
  }
  cln::cl_MI res = cln::recip(xm);
  return Integer(ry->retract(res));
}
} /* namespace CVC4 */
