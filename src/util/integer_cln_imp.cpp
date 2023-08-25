/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Tim King, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A multiprecision integer constant; wraps a CLN multiprecision integer.
 */

#include <cln/input.h>
#include <cln/integer_io.h>
#include <cln/modinteger.h>
#include <cln/numtheory.h>

#include <iostream>
#include <sstream>
#include <string>

#include "base/cvc5config.h"
#include "util/integer.h"

#ifndef CVC5_CLN_IMP
#error "This source should only ever be built if CVC5_CLN_IMP is on !"
#endif /* CVC5_CLN_IMP */

#include "base/check.h"

using namespace std;

namespace cvc5::internal {

signed int Integer::s_fastSignedIntMin = -(1 << 29);
signed int Integer::s_fastSignedIntMax = (1 << 29) - 1;
signed long Integer::s_slowSignedIntMin =
    (signed long)std::numeric_limits<signed int>::min();
signed long Integer::s_slowSignedIntMax =
    (signed long)std::numeric_limits<signed int>::max();

unsigned int Integer::s_fastUnsignedIntMax = (1 << 29) - 1;
unsigned long Integer::s_slowUnsignedIntMax =
    (unsigned long)std::numeric_limits<unsigned int>::max();

unsigned long Integer::s_signedLongMin =
    std::numeric_limits<signed long>::min();
unsigned long Integer::s_signedLongMax =
    std::numeric_limits<signed long>::max();
unsigned long Integer::s_unsignedLongMax =
    std::numeric_limits<unsigned long>::max();

Integer& Integer::operator=(const Integer& x)
{
  if (this == &x) return *this;
  d_value = x.d_value;
  return *this;
}

bool Integer::operator==(const Integer& y) const
{
  return d_value == y.d_value;
}

Integer Integer::operator-() const { return Integer(-(d_value)); }

bool Integer::operator!=(const Integer& y) const
{
  return d_value != y.d_value;
}

bool Integer::operator<(const Integer& y) const { return d_value < y.d_value; }

bool Integer::operator<=(const Integer& y) const
{
  return d_value <= y.d_value;
}

bool Integer::operator>(const Integer& y) const { return d_value > y.d_value; }

bool Integer::operator>=(const Integer& y) const
{
  return d_value >= y.d_value;
}

Integer Integer::operator+(const Integer& y) const
{
  return Integer(d_value + y.d_value);
}

Integer& Integer::operator+=(const Integer& y)
{
  d_value += y.d_value;
  return *this;
}

Integer Integer::operator-(const Integer& y) const
{
  return Integer(d_value - y.d_value);
}

Integer& Integer::operator-=(const Integer& y)
{
  d_value -= y.d_value;
  return *this;
}

Integer Integer::operator*(const Integer& y) const
{
  return Integer(d_value * y.d_value);
}

Integer& Integer::operator*=(const Integer& y)
{
  d_value *= y.d_value;
  return *this;
}

Integer Integer::bitwiseOr(const Integer& y) const
{
  return Integer(cln::logior(d_value, y.d_value));
}

Integer Integer::bitwiseAnd(const Integer& y) const
{
  return Integer(cln::logand(d_value, y.d_value));
}

Integer Integer::bitwiseXor(const Integer& y) const
{
  return Integer(cln::logxor(d_value, y.d_value));
}

Integer Integer::bitwiseNot() const { return Integer(cln::lognot(d_value)); }

Integer Integer::multiplyByPow2(uint32_t pow) const
{
  cln::cl_I ipow(pow);
  return Integer(d_value << ipow);
}

bool Integer::isBitSet(uint32_t i) const
{
  return !extractBitRange(1, i).isZero();
}

void Integer::setBit(uint32_t i, bool value)
{
  cln::cl_I mask(1);
  mask = mask << i;
  if (value)
  {
    d_value = cln::logior(d_value, mask);
  }
  else
  {
    mask = cln::lognot(mask);
    d_value = cln::logand(d_value, mask);
  }
}

Integer Integer::oneExtend(uint32_t size, uint32_t amount) const
{
  Assert((*this) < Integer(1).multiplyByPow2(size));
  cln::cl_byte range(amount, size);
  cln::cl_I allones = (cln::cl_I(1) << (size + amount)) - 1;  // 2^size - 1
  Integer temp(allones);

  return Integer(cln::deposit_field(allones, d_value, range));
}

uint32_t Integer::toUnsignedInt() const { return cln::cl_I_to_uint(d_value); }

Integer Integer::extractBitRange(uint32_t bitCount, uint32_t low) const
{
  cln::cl_byte range(bitCount, low);
  return Integer(cln::ldb(d_value, range));
}

Integer Integer::floorDivideQuotient(const Integer& y) const
{
  return Integer(cln::floor1(d_value, y.d_value));
}

Integer Integer::floorDivideRemainder(const Integer& y) const
{
  return Integer(cln::floor2(d_value, y.d_value).remainder);
}

void Integer::floorQR(Integer& q,
                      Integer& r,
                      const Integer& x,
                      const Integer& y)
{
  cln::cl_I_div_t res = cln::floor2(x.d_value, y.d_value);
  q.d_value = res.quotient;
  r.d_value = res.remainder;
}

Integer Integer::ceilingDivideQuotient(const Integer& y) const
{
  return Integer(cln::ceiling1(d_value, y.d_value));
}

Integer Integer::ceilingDivideRemainder(const Integer& y) const
{
  return Integer(cln::ceiling2(d_value, y.d_value).remainder);
}

void Integer::euclidianQR(Integer& q,
                          Integer& r,
                          const Integer& x,
                          const Integer& y)
{
  // compute the floor and then fix the value up if needed.
  floorQR(q, r, x, y);

  if (r.strictlyNegative())
  {
    // if r < 0
    // abs(r) < abs(y)
    // - abs(y) < r < 0, then 0 < r + abs(y) < abs(y)
    // n = y * q + r
    // n = y * q - abs(y) + r + abs(y)
    if (r.sgn() >= 0)
    {
      // y = abs(y)
      // n = y * q - y + r + y
      // n = y * (q-1) + (r+y)
      q -= 1;
      r += y;
    }
    else
    {
      // y = -abs(y)
      // n = y * q + y + r - y
      // n = y * (q+1) + (r-y)
      q += 1;
      r -= y;
    }
  }
}

Integer Integer::euclidianDivideQuotient(const Integer& y) const
{
  Integer q, r;
  euclidianQR(q, r, *this, y);
  return q;
}

Integer Integer::euclidianDivideRemainder(const Integer& y) const
{
  Integer q, r;
  euclidianQR(q, r, *this, y);
  return r;
}

Integer Integer::exactQuotient(const Integer& y) const
{
  Assert(y.divides(*this));
  return Integer(cln::exquo(d_value, y.d_value));
}

Integer Integer::modByPow2(uint32_t exp) const
{
  cln::cl_byte range(exp, 0);
  return Integer(cln::ldb(d_value, range));
}

Integer Integer::divByPow2(uint32_t exp) const { return d_value >> exp; }

Integer Integer::pow(uint32_t exp) const
{
  if (exp == 0)
  {
    return Integer(1);
  }
  else
  {
    Assert(exp > 0);
    cln::cl_I result = cln::expt_pos(d_value, exp);
    return Integer(result);
  }
}

Integer Integer::gcd(const Integer& y) const
{
  cln::cl_I result = cln::gcd(d_value, y.d_value);
  return Integer(result);
}

Integer Integer::lcm(const Integer& y) const
{
  cln::cl_I result = cln::lcm(d_value, y.d_value);
  return Integer(result);
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
  Assert(m > 0) << "m must be greater than zero";
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

bool Integer::divides(const Integer& y) const
{
  cln::cl_I result = cln::rem(y.d_value, d_value);
  return cln::zerop(result);
}

Integer Integer::abs() const { return d_value >= 0 ? *this : -*this; }

std::string Integer::toString(int base) const
{
  std::stringstream ss;
  switch (base)
  {
    case 2: fprintbinary(ss, d_value); break;
    case 8: fprintoctal(ss, d_value); break;
    case 10: fprintdecimal(ss, d_value); break;
    case 16: fprinthexadecimal(ss, d_value); break;
    default: throw Exception("Unhandled base in Integer::toString()");
  }
  std::string output = ss.str();
  for (unsigned i = 0; i <= output.length(); ++i)
  {
    if (isalpha(output[i]))
    {
      output.replace(i, 1, 1, tolower(output[i]));
    }
  }

  return output;
}

int Integer::sgn() const
{
  cln::cl_I sgn = cln::signum(d_value);
  return cln::cl_I_to_int(sgn);
}

bool Integer::strictlyPositive() const { return cln::plusp(d_value); }

bool Integer::strictlyNegative() const { return cln::minusp(d_value); }

bool Integer::isZero() const { return cln::zerop(d_value); }

bool Integer::isOne() const { return d_value == 1; }

bool Integer::isNegativeOne() const { return d_value == -1; }

void Integer::parseInt(const std::string& s, unsigned base)
{
  cln::cl_read_flags flags;
  flags.syntax = cln::syntax_integer;
  flags.lsyntax = cln::lsyntax_standard;
  flags.rational_base = base;
  if (base == 0)
  {
    // infer base in a manner consistent with GMP
    if (s[0] == '0')
    {
      flags.lsyntax = cln::lsyntax_commonlisp;
      std::string st = s;
      if (s[1] == 'X' || s[1] == 'x')
      {
        st.replace(0, 2, "#x");
      }
      else if (s[1] == 'B' || s[1] == 'b')
      {
        st.replace(0, 2, "#b");
      }
      else
      {
        st.replace(0, 1, "#o");
      }
      readInt(flags, st, base);
      return;
    }
    else
    {
      flags.rational_base = 10;
    }
  }
  readInt(flags, s, base);
}

void Integer::readInt(const cln::cl_read_flags& flags,
                      const std::string& s,
                      unsigned base)
{
  try
  {
    // Removing leading zeroes, CLN has a bug for these inputs up to and
    // including CLN v1.3.2.
    // See
    // http://www.ginac.de/CLN/cln.git/?a=commit;h=4a477b0cc3dd7fbfb23b25090ff8c8869c8fa21a
    // for details.
    size_t pos = s.find_first_not_of('0');
    if (pos == std::string::npos)
    {
      d_value = cln::read_integer(flags, "0", NULL, NULL);
    }
    else
    {
      const char* cstr = s.c_str();
      const char* start = cstr + pos;
      const char* end = cstr + s.length();
      d_value = cln::read_integer(flags, start, end, NULL);
    }
  }
  catch (...)
  {
    std::stringstream ss;
    ss << "Integer() failed to parse value \"" << s << "\" in base " << base;
    throw std::invalid_argument(ss.str());
  }
}

bool Integer::fitsSignedInt() const
{
  // http://www.ginac.de/CLN/cln.html#Conversions
  // TODO improve performance
  Assert(s_slowSignedIntMin <= s_fastSignedIntMin);
  Assert(s_fastSignedIntMin <= s_fastSignedIntMax);
  Assert(s_fastSignedIntMax <= s_slowSignedIntMax);

  return (d_value <= s_fastSignedIntMax || d_value <= s_slowSignedIntMax)
         && (d_value >= s_fastSignedIntMin || d_value >= s_slowSignedIntMax);
}

bool Integer::fitsUnsignedInt() const
{
  // TODO improve performance
  Assert(s_fastUnsignedIntMax <= s_slowUnsignedIntMax);
  return sgn() >= 0
         && (d_value <= s_fastUnsignedIntMax
             || d_value <= s_slowUnsignedIntMax);
}

signed int Integer::getSignedInt() const
{
  // ensure there isn't overflow
  Assert(fitsSignedInt()) << "Overflow detected in Integer::getSignedInt()";
  return cln::cl_I_to_int(d_value);
}

unsigned int Integer::getUnsignedInt() const
{
  // ensure there isn't overflow
  Assert(fitsUnsignedInt()) << "Overflow detected in Integer::getUnsignedInt()";
  return cln::cl_I_to_uint(d_value);
}

long Integer::getLong() const
{
  // ensure there isn't overflow
  Assert(d_value <= std::numeric_limits<long>::max())
      << "Overflow detected in Integer::getLong()";
  Assert(d_value >= std::numeric_limits<long>::min())
      << "Overflow detected in Integer::getLong()";
  return cln::cl_I_to_long(d_value);
}

unsigned long Integer::getUnsignedLong() const
{
  // ensure there isn't overflow
  Assert(d_value <= std::numeric_limits<unsigned long>::max())
      << "Overflow detected in Integer::getUnsignedLong()";
  Assert(d_value >= std::numeric_limits<unsigned long>::min())
      << "Overflow detected in Integer::getUnsignedLong()";
  return cln::cl_I_to_ulong(d_value);
}

int64_t Integer::getSigned64() const
{
  if constexpr (sizeof(int64_t) == sizeof(signed long int))
  {
    return getLong();
  }
  else
  {
    if (std::numeric_limits<long>::min() <= d_value
        && d_value <= std::numeric_limits<long>::max())
    {
      return getLong();
    }
    // ensure there isn't overflow
    Assert(d_value <= std::numeric_limits<int64_t>::max())
        << "Overflow detected in Integer::getSigned64()";
    Assert(d_value >= std::numeric_limits<int64_t>::min())
        << "Overflow detected in Integer::getSigned64()";
    return std::stoll(toString());
  }
}
uint64_t Integer::getUnsigned64() const
{
  if constexpr (sizeof(uint64_t) == sizeof(unsigned long int))
  {
    return getUnsignedLong();
  }
  else
  {
    if (std::numeric_limits<unsigned long>::min() <= d_value
        && d_value <= std::numeric_limits<unsigned long>::max())
    {
      return getUnsignedLong();
    }
    // ensure there isn't overflow
    Assert(d_value <= std::numeric_limits<uint64_t>::max())
        << "Overflow detected in Integer::getSigned64()";
    Assert(d_value >= std::numeric_limits<uint64_t>::min())
        << "Overflow detected in Integer::getSigned64()";
    return std::stoull(toString());
  }
}

size_t Integer::hash() const { return equal_hashcode(d_value); }

bool Integer::testBit(unsigned n) const { return cln::logbitp(n, d_value); }

unsigned Integer::isPow2() const
{
  if (d_value <= 0) return 0;
  // power2p returns n such that d_value = 2^(n-1)
  return cln::power2p(d_value);
}

size_t Integer::length() const
{
  int s = sgn();
  if (s == 0)
  {
    return 1;
  }
  else if (s < 0)
  {
    size_t len = cln::integer_length(d_value);
    /*If this is -2^n, return len+1 not len to stay consistent with the
     * definition above! From CLN's documentation of integer_length: This is
     * the smallest n >= 0 such that -2^n <= x < 2^n. If x > 0, this is the
     * unique n > 0 such that 2^(n-1) <= x < 2^n.
     */
    size_t ord2 = cln::ord2(d_value);
    return (len == ord2) ? (len + 1) : len;
  }
  else
  {
    return cln::integer_length(d_value);
  }
}

bool Integer::isProbablePrime() const { return cln::isprobprime(d_value); }

void Integer::extendedGcd(
    Integer& g, Integer& s, Integer& t, const Integer& a, const Integer& b)
{
  g.d_value = cln::xgcd(a.d_value, b.d_value, &s.d_value, &t.d_value);
}

const Integer& Integer::min(const Integer& a, const Integer& b)
{
  return (a <= b) ? a : b;
}

const Integer& Integer::max(const Integer& a, const Integer& b)
{
  return (a >= b) ? a : b;
}

std::ostream& operator<<(std::ostream& os, const Integer& n)
{
  return os << n.toString();
}
}  // namespace cvc5::internal
