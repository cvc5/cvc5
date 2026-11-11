/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A multiprecision integer constant; wraps a GMP multiprecision integer.
 */

#include <cmath>
#include <limits>
#include <numeric>
#include <sstream>
#include <string>

#include "base/check.h"
#include "base/cvc5config.h"
#include "util/gmp_util.h"
#include "util/integer.h"
#include "util/random.h"
#include "util/rational.h"

#ifndef CVC5_GMP_IMP
#error "This source should only ever be built if CVC5_GMP_IMP is on !"
#endif

using namespace std;

/** Declares `name`, a read-only GMP view of the Integer `x` (see mpzView). */
#define CVC5_MPZ_VIEW(name, x)                \
  mpz_t name##_tmp;                           \
  mp_limb_t name##_limbs[gmpz_limbs_per_u64]; \
  mpz_srcptr name = (x).mpzView(name##_tmp, name##_limbs)

namespace cvc5::internal {

namespace {
constexpr int64_t kMin64 = std::numeric_limits<int64_t>::min();

/** The Integer with value x. */
Integer fromU64(uint64_t x) { return Integer(x); }
}  // namespace

Integer::Integer(const char* s, unsigned base) { setMpz(mpz_class(s, base)); }

Integer::Integer(const std::string& s, unsigned base)
{
  setMpz(mpz_class(s, base));
}

#ifdef CVC5_NEED_INT64_T_OVERLOADS
Integer::Integer(uint64_t z)
{
  if (z < (uint64_t(1) << 62))
  {
    initSmall(static_cast<int64_t>(z));
  }
  else
  {
    mpz_class* p = new mpz_class();
    gmpz_set_uint64(p->get_mpz_t(), z);
    d_rep = toRep(p);
  }
}
#endif /* CVC5_NEED_INT64_T_OVERLOADS */

int Integer::cmpSlow(const Integer& y) const
{
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  return mpz_cmp(a, b);
}

Integer Integer::negSlow() const
{
  CVC5_MPZ_VIEW(a, *this);
  mpz_class r;
  mpz_neg(r.get_mpz_t(), a);
  return Integer(std::move(r));
}

Integer Integer::addSlow(const Integer& y) const
{
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class r;
  mpz_add(r.get_mpz_t(), a, b);
  return Integer(std::move(r));
}

Integer Integer::subSlow(const Integer& y) const
{
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class r;
  mpz_sub(r.get_mpz_t(), a, b);
  return Integer(std::move(r));
}

Integer Integer::mulSlow(const Integer& y) const
{
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class r;
  mpz_mul(r.get_mpz_t(), a, b);
  return Integer(std::move(r));
}

size_t Integer::hashSlow() const
{
  // the GMP form of an integer that fits must hash like the inline form
  return gmpz_hash(bigRef().get_mpz_t());
}

Integer Integer::bitwiseOr(const Integer& y) const
{
  if (bothSmall(y))
  {
    return Integer(smallVal() | y.smallVal());
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class result;
  mpz_ior(result.get_mpz_t(), a, b);
  return Integer(std::move(result));
}

Integer Integer::bitwiseAnd(const Integer& y) const
{
  if (bothSmall(y))
  {
    return Integer(smallVal() & y.smallVal());
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class result;
  mpz_and(result.get_mpz_t(), a, b);
  return Integer(std::move(result));
}

Integer Integer::bitwiseXor(const Integer& y) const
{
  if (bothSmall(y))
  {
    return Integer(smallVal() ^ y.smallVal());
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class result;
  mpz_xor(result.get_mpz_t(), a, b);
  return Integer(std::move(result));
}

Integer Integer::bitwiseNot() const
{
  if (isSmallRep())
  {
    return Integer(~smallVal());
  }
  CVC5_MPZ_VIEW(a, *this);
  mpz_class result;
  mpz_com(result.get_mpz_t(), a);
  return Integer(std::move(result));
}

Integer Integer::multiplyByPow2(uint32_t pow) const
{
  CVC5_MPZ_VIEW(a, *this);
  mpz_class result;
  mpz_mul_2exp(result.get_mpz_t(), a, pow);
  return Integer(std::move(result));
}

void Integer::setBit(uint32_t i, bool value)
{
  CVC5_MPZ_VIEW(a, *this);
  mpz_class r(a);
  if (value)
  {
    mpz_setbit(r.get_mpz_t(), i);
  }
  else
  {
    mpz_clrbit(r.get_mpz_t(), i);
  }
  *this = Integer(std::move(r));
}

bool Integer::isBitSet(uint32_t i) const
{
  return !extractBitRange(1, i).isZero();
}

Integer Integer::oneExtend(uint32_t size, uint32_t amount) const
{
  // check that the size is accurate
  Assert((*this) < Integer(1).multiplyByPow2(size));
  CVC5_MPZ_VIEW(a, *this);
  mpz_class res(a);
  for (unsigned i = size; i < size + amount; ++i)
  {
    mpz_setbit(res.get_mpz_t(), i);
  }

  return Integer(std::move(res));
}

uint32_t Integer::toUnsignedInt() const
{
  CVC5_MPZ_VIEW(a, *this);
  return mpz_get_ui(a);
}

Integer Integer::extractBitRange(uint32_t bitCount, uint32_t low) const
{
  // bitCount = high-low+1
  uint32_t high = low + bitCount - 1;
  // — Function: void mpz_fdiv_r_2exp (mpz_t r, mpz_t n, mp_bitcnt_t b)
  CVC5_MPZ_VIEW(a, *this);
  mpz_class rem, div;
  mpz_fdiv_r_2exp(rem.get_mpz_t(), a, high + 1);
  mpz_fdiv_q_2exp(div.get_mpz_t(), rem.get_mpz_t(), low);

  return Integer(std::move(div));
}

Integer Integer::floorDivideQuotient(const Integer& y) const
{
  if (bothSmall(y) && y.smallVal() != 0
      && !(smallVal() == kMin64 && y.smallVal() == -1))
  {
    int64_t q = smallVal() / y.smallVal();
    int64_t r = smallVal() % y.smallVal();
    return Integer(r != 0 && ((r < 0) != (y.smallVal() < 0)) ? q - 1 : q);
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class q;
  mpz_fdiv_q(q.get_mpz_t(), a, b);
  return Integer(std::move(q));
}

Integer Integer::floorDivideRemainder(const Integer& y) const
{
  if (bothSmall(y) && y.smallVal() != 0
      && !(smallVal() == kMin64 && y.smallVal() == -1))
  {
    int64_t r = smallVal() % y.smallVal();
    return Integer(r != 0 && ((r < 0) != (y.smallVal() < 0)) ? r + y.smallVal()
                                                             : r);
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class r;
  mpz_fdiv_r(r.get_mpz_t(), a, b);
  return Integer(std::move(r));
}

void Integer::floorQR(Integer& q,
                      Integer& r,
                      const Integer& x,
                      const Integer& y)
{
  if (x.bothSmall(y) && y.smallVal() != 0
      && !(x.smallVal() == kMin64 && y.smallVal() == -1))
  {
    int64_t qq = x.smallVal() / y.smallVal();
    int64_t rr = x.smallVal() % y.smallVal();
    if (rr != 0 && ((rr < 0) != (y.smallVal() < 0)))
    {
      qq -= 1;
      rr += y.smallVal();
    }
    q = Integer(qq);
    r = Integer(rr);
    return;
  }
  CVC5_MPZ_VIEW(a, x);
  CVC5_MPZ_VIEW(b, y);
  mpz_class qq, rr;
  mpz_fdiv_qr(qq.get_mpz_t(), rr.get_mpz_t(), a, b);
  q = Integer(std::move(qq));
  r = Integer(std::move(rr));
}

Integer Integer::ceilingDivideQuotient(const Integer& y) const
{
  if (bothSmall(y) && y.smallVal() != 0
      && !(smallVal() == kMin64 && y.smallVal() == -1))
  {
    int64_t qq = smallVal() / y.smallVal();
    int64_t rr = smallVal() % y.smallVal();
    if (rr != 0 && ((rr > 0) == (y.smallVal() > 0)))
    {
      qq += 1;
    }
    return Integer(qq);
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class q;
  mpz_cdiv_q(q.get_mpz_t(), a, b);
  return Integer(std::move(q));
}

Integer Integer::ceilingDivideRemainder(const Integer& y) const
{
  if (bothSmall(y) && y.smallVal() != 0
      && !(smallVal() == kMin64 && y.smallVal() == -1))
  {
    int64_t rr = smallVal() % y.smallVal();
    if (rr != 0 && ((rr > 0) == (y.smallVal() > 0)))
    {
      rr -= y.smallVal();
    }
    return Integer(rr);
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class r;
  mpz_cdiv_r(r.get_mpz_t(), a, b);
  return Integer(std::move(r));
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
  if (bothSmall(y) && !(smallVal() == kMin64 && y.smallVal() == -1))
  {
    return Integer(smallVal() / y.smallVal());
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class q;
  mpz_divexact(q.get_mpz_t(), a, b);
  return Integer(std::move(q));
}

Integer Integer::modByPow2(uint32_t exp) const
{
  CVC5_MPZ_VIEW(a, *this);
  mpz_class res;
  mpz_fdiv_r_2exp(res.get_mpz_t(), a, exp);
  return Integer(std::move(res));
}

Integer Integer::divByPow2(uint32_t exp) const
{
  CVC5_MPZ_VIEW(a, *this);
  mpz_class res;
  mpz_fdiv_q_2exp(res.get_mpz_t(), a, exp);
  return Integer(std::move(res));
}

Integer Integer::pow(uint32_t exp) const
{
  CVC5_MPZ_VIEW(a, *this);
  mpz_class result;
  mpz_pow_ui(result.get_mpz_t(), a, exp);
  return Integer(std::move(result));
}

Integer Integer::gcd(const Integer& y) const
{
  if (bothSmall(y))
  {
    return fromU64(std::gcd(absU64(smallVal()), absU64(y.smallVal())));
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class result;
  mpz_gcd(result.get_mpz_t(), a, b);
  return Integer(std::move(result));
}

Integer Integer::lcm(const Integer& y) const
{
  if (bothSmall(y))
  {
    uint64_t a = absU64(smallVal()), b = absU64(y.smallVal());
    if (a == 0 || b == 0)
    {
      return Integer(0);
    }
    uint64_t l;
    if (!__builtin_mul_overflow(a / std::gcd(a, b), b, &l))
    {
      return fromU64(l);
    }
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  mpz_class result;
  mpz_lcm(result.get_mpz_t(), a, b);
  return Integer(std::move(result));
}

Integer Integer::modAdd(const Integer& y, const Integer& m) const
{
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  CVC5_MPZ_VIEW(c, m);
  mpz_class res;
  mpz_add(res.get_mpz_t(), a, b);
  mpz_mod(res.get_mpz_t(), res.get_mpz_t(), c);
  return Integer(std::move(res));
}

Integer Integer::modMultiply(const Integer& y, const Integer& m) const
{
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  CVC5_MPZ_VIEW(c, m);
  mpz_class res;
  mpz_mul(res.get_mpz_t(), a, b);
  mpz_mod(res.get_mpz_t(), res.get_mpz_t(), c);
  return Integer(std::move(res));
}

Integer Integer::modInverse(const Integer& m) const
{
  Assert(m > 0) << "m must be greater than zero";
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, m);
  mpz_class res;
  if (mpz_invert(res.get_mpz_t(), a, b) == 0)
  {
    return Integer(-1);
  }
  return Integer(std::move(res));
}

bool Integer::divides(const Integer& y) const
{
  if (bothSmall(y))
  {
    // mpz_divisible_p: only 0 is divisible by 0
    return smallVal() == 0 ? y.smallVal() == 0
                           : absU64(y.smallVal()) % absU64(smallVal()) == 0;
  }
  CVC5_MPZ_VIEW(a, *this);
  CVC5_MPZ_VIEW(b, y);
  int res = mpz_divisible_p(b, a);
  return res != 0;
}

std::string Integer::toString(int base) const
{
  if (isSmallRep() && base == 10)
  {
    return std::to_string(smallVal());
  }
  CVC5_MPZ_VIEW(a, *this);
  return mpz_class(a).get_str(base);
}

bool Integer::fitsSignedInt() const
{
  return isSmallRep() ? smallVal() >= std::numeric_limits<int>::min()
                            && smallVal() <= std::numeric_limits<int>::max()
                      : bigRef().fits_sint_p();
}

bool Integer::fitsUnsignedInt() const
{
  return isSmallRep()
             ? smallVal() >= 0
                   && smallVal() <= std::numeric_limits<unsigned int>::max()
             : bigRef().fits_uint_p();
}

signed int Integer::getSignedInt() const
{
  Assert(fitsSignedInt()) << "Overflow detected in Integer::getSignedInt().";
  CVC5_MPZ_VIEW(a, *this);
  return (signed int)mpz_get_si(a);
}

unsigned int Integer::getUnsignedInt() const
{
  Assert(fitsUnsignedInt()) << "Overflow detected in Integer::getUnsignedInt()";
  CVC5_MPZ_VIEW(a, *this);
  return (unsigned int)mpz_get_ui(a);
}

long Integer::getLong() const
{
  CVC5_MPZ_VIEW(a, *this);
  // ensure there it fits
  Assert(mpz_fits_slong_p(a) != 0)
      << "Overflow detected in Integer::getLong().";
  return mpz_get_si(a);
}

unsigned long Integer::getUnsignedLong() const
{
  CVC5_MPZ_VIEW(a, *this);
  // ensure that it fits
  Assert(mpz_fits_ulong_p(a) != 0)
      << "Overflow detected in Integer::getUnsignedLong().";
  return mpz_get_ui(a);
}

int64_t Integer::getSigned64() const
{
  if constexpr (sizeof(int64_t) == sizeof(signed long int))
  {
    return getLong();
  }
  else
  {
    CVC5_MPZ_VIEW(a, *this);
    if (mpz_fits_slong_p(a) != 0)
    {
      return getLong();
    }
    try
    {
      return std::stoll(toString());
    }
    catch (const std::exception& e)
    {
      DebugUnhandled() << "Overflow detected in Integer::getSigned64().";
    }
  }
  return 0;
}

uint64_t Integer::getUnsigned64() const
{
  if constexpr (sizeof(uint64_t) == sizeof(unsigned long int))
  {
    return getUnsignedLong();
  }
  else
  {
    CVC5_MPZ_VIEW(a, *this);
    if (mpz_fits_ulong_p(a) != 0)
    {
      return getUnsignedLong();
    }
    try
    {
      Assert(sgn() >= 0) << "Overflow detected in Integer::getUnsigned64().";
      return std::stoull(toString());
    }
    catch (const std::exception& e)
    {
      DebugUnhandled() << "Overflow detected in Integer::getUnsigned64().";
    }
  }
  return 0;
}

bool Integer::testBit(unsigned n) const
{
  CVC5_MPZ_VIEW(a, *this);
  return mpz_tstbit(a, n);
}

unsigned Integer::isPow2() const
{
  if (sgn() <= 0) return 0;
  // check that the number of ones in the binary represenation is 1
  CVC5_MPZ_VIEW(a, *this);
  if (mpz_popcount(a) == 1)
  {
    // return the index of the first one plus 1
    return mpz_scan1(a, 0) + 1;
  }
  return 0;
}

size_t Integer::length() const
{
  if (sgn() == 0)
  {
    return 1;
  }
  if (isSmallRep())
  {
    return 64 - __builtin_clzll(absU64(smallVal()));
  }
  return mpz_sizeinbase(bigRef().get_mpz_t(), 2);
}

bool Integer::isProbablePrime() const
{
  CVC5_MPZ_VIEW(a, *this);
  return mpz_probab_prime_p(a, 30) > 0;
}

void Integer::extendedGcd(
    Integer& g, Integer& s, Integer& t, const Integer& a, const Integer& b)
{
  CVC5_MPZ_VIEW(va, a);
  CVC5_MPZ_VIEW(vb, b);
  mpz_class gg, ss, tt;
  mpz_gcdext(gg.get_mpz_t(), ss.get_mpz_t(), tt.get_mpz_t(), va, vb);
  g = Integer(std::move(gg));
  s = Integer(std::move(ss));
  t = Integer(std::move(tt));
}

const Integer& Integer::min(const Integer& a, const Integer& b)
{
  return (a <= b) ? a : b;
}

const Integer& Integer::max(const Integer& a, const Integer& b)
{
  return (a >= b) ? a : b;
}

Integer Integer::mkRandom(uint32_t nbits)
{
  Assert(nbits > 0);
  mpz_class res;
  Random& rnd = Random::getRandom();
  mpz_urandomb(res.get_mpz_t(), *rnd.getGMPRandstate(), nbits);
  return Integer(std::move(res));
}

}  // namespace cvc5::internal
