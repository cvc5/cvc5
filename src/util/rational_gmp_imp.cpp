/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A multi-precision rational constant.
 */
#include <cmath>
#include <limits>
#include <numeric>
#include <sstream>
#include <string>

#include "base/cvc5config.h"
#include "util/rational.h"

#ifndef CVC5_GMP_IMP  // Make sure this comes after base/cvc5config.h
#error "This source should only ever be built if CVC5_GMP_IMP is on !"
#endif /* CVC5_GMP_IMP */

#include "base/check.h"

/** Declares `name`, a read-only GMP view of the Rational `x` (see mpqView). */
#define CVC5_MPQ_VIEW(name, x)                                            \
  mpq_t name##_tmp;                                                       \
  mpz_t name##_tn, name##_td;                                             \
  mp_limb_t name##_ln[gmpz_limbs_per_u64], name##_ld[gmpz_limbs_per_u64]; \
  mpq_srcptr name =                                                       \
      (x).mpqView(name##_tmp, name##_tn, name##_td, name##_ln, name##_ld)

namespace cvc5::internal {

namespace {

using u128 = unsigned __int128;

bool fits64(__int128 v)
{
  return v >= std::numeric_limits<int64_t>::min()
         && v <= std::numeric_limits<int64_t>::max();
}

u128 abs128(__int128 v) { return v < 0 ? -static_cast<u128>(v) : v; }

u128 gcd128(u128 a, u128 b)
{
  while (b != 0)
  {
    if ((a >> 64) == 0 && (b >> 64) == 0)
    {
      return std::gcd(static_cast<uint64_t>(a), static_cast<uint64_t>(b));
    }
    u128 t = a % b;
    a = b;
    b = t;
  }
  return a;
}

/** Sets z to the value v. */
void setMpz128(mpz_ptr z, __int128 v)
{
  u128 a = abs128(v);
  uint64_t w[2] = {static_cast<uint64_t>(a), static_cast<uint64_t>(a >> 64)};
  mpz_import(z, 2, -1, sizeof(uint64_t), 0, 0, w);
  if (v < 0)
  {
    mpz_neg(z, z);
  }
}

/**
 * If the numerator and denominator of x fit into an int64_t, sets n and d to
 * them and returns true.
 */
bool mpqGetInt64(mpq_srcptr x, int64_t* n, int64_t* d)
{
  return gmpz_get_int64(mpq_numref(x), n) && gmpz_get_int64(mpq_denref(x), d);
}

}  // namespace

std::ostream& operator<<(std::ostream& os, const Rational& q)
{
  return os << q.toString();
}

/* Computes a rational given a decimal string. The rational
 * version of <code>xxx.yyy</code> is <code>xxxyyy/(10^3)</code>.
 */
Rational Rational::fromDecimal(const std::string& dec)
{
  using std::string;
  // Find the decimal point, if there is one
  string::size_type i(dec.find("."));
  if (i != string::npos)
  {
    /* Erase the decimal point, so we have just the numerator. */
    Integer numerator(string(dec).erase(i, 1));

    /* Compute the denominator: 10 raise to the number of decimal places */
    int decPlaces = dec.size() - (i + 1);
    Integer denominator(Integer(10).pow(decPlaces));

    return Rational(numerator, denominator);
  }
  else
  {
    /* No decimal point, assume it's just an integer. */
    return Rational(dec);
  }
}

Rational::Rational(const char* s, unsigned base)
{
  mpq_class v(s, base);
  v.canonicalize();
  setMpq(std::move(v));
}

Rational::Rational(const std::string& s, unsigned base)
{
  mpq_class v(s, base);
  v.canonicalize();
  setMpq(std::move(v));
}

Rational::Rational(const Integer& n, const Integer& d)
{
  if (n.isSmallRep() && d.isSmallRep())
  {
    setParts(n.smallVal(), d.smallVal());
    return;
  }
  mpz_t tn, td;
  mp_limb_t ln[gmpz_limbs_per_u64], ld[gmpz_limbs_per_u64];
  mpq_class v(mpz_class(n.mpzView(tn, ln)), mpz_class(d.mpzView(td, ld)));
  v.canonicalize();
  setMpq(std::move(v));
}

void Rational::setParts(__int128 n, __int128 d)
{
  if (d == 0)
  {
    // let GMP report the division by zero as before
    mpq_class v;
    setMpz128(mpq_numref(v.get_mpq_t()), n);
    mpz_set_ui(mpq_denref(v.get_mpq_t()), 0);
    v.canonicalize();
    setMpq(std::move(v));
    return;
  }
  if (d < 0)
  {
    n = -n;
    d = -d;
  }
  u128 g = gcd128(abs128(n), static_cast<u128>(d));
  if (g > 1)
  {
    n /= static_cast<__int128>(g);
    d /= static_cast<__int128>(g);
  }
  if (fits64(n) && fits64(d))
  {
    setSmall(static_cast<int64_t>(n), static_cast<int64_t>(d));
    return;
  }
  mpq_class* v = new mpq_class();
  setMpz128(mpq_numref(v->get_mpq_t()), n);
  setMpz128(mpq_denref(v->get_mpq_t()), d);
  initBig(v);
}

void Rational::setMpq(const mpq_class& x)
{
  int64_t n, d;
  if (mpqGetInt64(x.get_mpq_t(), &n, &d))
  {
    // the value is assumed to be canonical, but only use the inline form if
    // it is, so that values that are not keep their (GMP) behavior
    if (d > 0 && std::gcd(Integer::absU64(n), static_cast<uint64_t>(d)) == 1)
    {
      setSmall(n, d);
      return;
    }
  }
  initBig(new mpq_class(x));
}

void Rational::setMpq(mpq_class&& x)
{
  int64_t n, d;
  if (mpqGetInt64(x.get_mpq_t(), &n, &d))
  {
    if (d > 0 && std::gcd(Integer::absU64(n), static_cast<uint64_t>(d)) == 1)
    {
      setSmall(n, d);
      return;
    }
  }
  initBig(new mpq_class(std::move(x)));
}

void Rational::setMpqCanonical()
{
  bigRef().canonicalize();
  int64_t n, d;
  if (mpqGetInt64(bigRef().get_mpq_t(), &n, &d))
  {
    setSmallCanonical(n, d);
  }
}

void Rational::promote()
{
  mpq_class* v = new mpq_class();
  gmpz_set_int64(mpq_numref(v->get_mpq_t()), d_num);
  gmpz_set_int64(mpq_denref(v->get_mpq_t()), d_den);
  initBig(v);
}

mpq_srcptr Rational::mpqView(
    mpq_t tmp, mpz_t tn, mpz_t td, mp_limb_t* ln, mp_limb_t* ld) const
{
  if (!isSmallRep())
  {
    return bigRef().get_mpq_t();
  }
  gmpz_limbs_from_u64(ln, Integer::absU64(d_num));
  gmpz_limbs_from_u64(ld, static_cast<uint64_t>(d_den));
  // mpz_roinit_n ignores high zero limbs
  mpz_srcptr n = mpz_roinit_n(
      tn, ln, d_num < 0 ? -gmpz_limbs_per_u64 : gmpz_limbs_per_u64);
  mpz_srcptr d = mpz_roinit_n(td, ld, gmpz_limbs_per_u64);
  // a read-only rational made of the two read-only integers
  *mpq_numref(tmp) = *n;
  *mpq_denref(tmp) = *d;
  return tmp;
}

Rational Rational::fromCanonical(__int128 n, __int128 d)
{
  if (fits64(n) && fits64(d))
  {
    Rational r;
    r.d_num = static_cast<int64_t>(n);
    r.d_den = static_cast<int64_t>(d);
    return r;
  }
  mpq_class v;
  setMpz128(mpq_numref(v.get_mpq_t()), n);
  setMpz128(mpq_denref(v.get_mpq_t()), d);
  return Rational(std::move(v));
}

Rational Rational::mulParts(__int128 an, uint64_t ad, __int128 bn, uint64_t bd)
{
  if (an == 0 || bn == 0)
  {
    return Rational(0);
  }
  uint64_t g1 = std::gcd(static_cast<uint64_t>(abs128(an)), bd);
  uint64_t g2 = std::gcd(static_cast<uint64_t>(abs128(bn)), ad);
  __int128 n = (an / g1) * (bn / g2);
  __int128 d = static_cast<__int128>(ad / g2) * (bd / g1);
  return fromCanonical(n, d);
}

int Rational::cmpSlow(const Rational& y) const
{
  CVC5_MPQ_VIEW(a, *this);
  CVC5_MPQ_VIEW(b, y);
  return mpq_cmp(a, b);
}

Rational Rational::negSlow() const
{
  CVC5_MPQ_VIEW(a, *this);
  mpq_class r;
  mpq_neg(r.get_mpq_t(), a);
  return Rational(std::move(r));
}

Rational Rational::addSlow(const Rational& y, bool subtract) const
{
  if (bothSmall(y))
  {
    // Knuth, TAOCP vol. 2, 4.5.1
    __int128 a = d_num;
    __int128 b = subtract ? -static_cast<__int128>(y.d_num) : y.d_num;
    uint64_t ad = d_den, bd = y.d_den;
    uint64_t g = std::gcd(ad, bd);
    if (g == 1)
    {
      return fromCanonical(a * bd + b * ad, static_cast<__int128>(ad) * bd);
    }
    __int128 t = a * (bd / g) + b * (ad / g);
    if (t == 0)
    {
      return Rational(0);
    }
    uint64_t g2 = std::gcd(static_cast<uint64_t>(abs128(t) % g), g);
    return fromCanonical(t / g2, static_cast<__int128>(ad / g) * (bd / g2));
  }
  CVC5_MPQ_VIEW(a, *this);
  CVC5_MPQ_VIEW(b, y);
  mpq_class r;
  if (subtract)
  {
    mpq_sub(r.get_mpq_t(), a, b);
  }
  else
  {
    mpq_add(r.get_mpq_t(), a, b);
  }
  return Rational(std::move(r));
}

Rational Rational::mulSlow(const Rational& y) const
{
  if (bothSmall(y))
  {
    return mulParts(d_num, d_den, y.d_num, y.d_den);
  }
  CVC5_MPQ_VIEW(a, *this);
  CVC5_MPQ_VIEW(b, y);
  mpq_class r;
  mpq_mul(r.get_mpq_t(), a, b);
  return Rational(std::move(r));
}

Rational Rational::divSlow(const Rational& y) const
{
  if (bothSmall(y) && y.d_num != 0)
  {
    // multiply by the inverse of y
    __int128 in = y.d_num < 0 ? -static_cast<__int128>(y.d_den) : y.d_den;
    return mulParts(d_num, d_den, in, Integer::absU64(y.d_num));
  }
  CVC5_MPQ_VIEW(a, *this);
  CVC5_MPQ_VIEW(b, y);
  mpq_class r;
  mpq_div(r.get_mpq_t(), a, b);
  return Rational(std::move(r));
}

size_t Rational::hashSlow() const
{
  size_t numeratorHash = gmpz_hash(bigRef().get_num_mpz_t());
  size_t denominatorHash = gmpz_hash(bigRef().get_den_mpz_t());
  return numeratorHash ^ denominatorHash;
}

Integer Rational::floor() const
{
  if (isSmallRep())
  {
    int64_t q = d_num / d_den;
    if (d_num % d_den != 0 && d_num < 0)
    {
      q -= 1;
    }
    return Integer(q);
  }
  mpz_class q;
  mpz_fdiv_q(q.get_mpz_t(), bigRef().get_num_mpz_t(), bigRef().get_den_mpz_t());
  return Integer(std::move(q));
}

Integer Rational::ceiling() const
{
  if (isSmallRep())
  {
    int64_t q = d_num / d_den;
    if (d_num % d_den != 0 && d_num > 0)
    {
      q += 1;
    }
    return Integer(q);
  }
  mpz_class q;
  mpz_cdiv_q(q.get_mpz_t(), bigRef().get_num_mpz_t(), bigRef().get_den_mpz_t());
  return Integer(std::move(q));
}

double Rational::getDouble() const
{
  CVC5_MPQ_VIEW(a, *this);
  return mpq_get_d(a);
}

std::string Rational::toString(int base) const
{
  if (isSmallRep() && base == 10)
  {
    return d_den == 1 ? std::to_string(d_num)
                      : std::to_string(d_num) + "/" + std::to_string(d_den);
  }
  CVC5_MPQ_VIEW(a, *this);
  return mpq_class(a).get_str(base);
}

int Rational::absCmp(const Rational& q) const
{
  const Rational& r = *this;
  int rsgn = r.sgn();
  int qsgn = q.sgn();
  if (rsgn == 0)
  {
    return (qsgn == 0) ? 0 : -1;
  }
  else if (qsgn == 0)
  {
    Assert(rsgn != 0);
    return 1;
  }
  else if ((rsgn > 0) && (qsgn > 0))
  {
    return r.cmp(q);
  }
  else if ((rsgn < 0) && (qsgn < 0))
  {
    // if r < q < 0, q.cmp(r) = +1, (r.abs()).cmp(q.abs()) = +1
    // if q < r < 0, q.cmp(r) = -1, (r.abs()).cmp(q.abs()) = -1
    // if q = r < 0, q.cmp(r) =  0, (r.abs()).cmp(q.abs()) =  0
    return q.cmp(r);
  }
  else if ((rsgn < 0) && (qsgn > 0))
  {
    Rational rpos = -r;
    return rpos.cmp(q);
  }
  else
  {
    Assert(rsgn > 0 && (qsgn < 0));
    Rational qpos = -q;
    return r.cmp(qpos);
  }
}

/** Return an exact rational for a double d. */
std::optional<Rational> Rational::fromDouble(double d)
{
  using namespace std;
  if (isfinite(d))
  {
    mpq_class q;
    mpq_set_d(q.get_mpq_t(), d);
    return Rational(std::move(q));
  }
  return std::optional<Rational>();
}

}  // namespace cvc5::internal
