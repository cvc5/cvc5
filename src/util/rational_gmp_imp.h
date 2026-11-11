/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Multiprecision rational constants; wraps a GMP multiprecision rational.
 */

#include "cvc5_public.h"

#ifndef CVC5__RATIONAL_H
#define CVC5__RATIONAL_H

#include <gmp.h>

#include <cstdint>
#include <limits>
#include <new>
#include <numeric>
#include <optional>
#include <string>
#include <utility>

#include "util/gmp_util.h"
#include "util/integer.h"

namespace cvc5::internal {

/**
 * A multi-precision rational constant.
 * This stores the rational as a pair of multi-precision integers,
 * one for the numerator and one for the denominator.
 * The number is always stored so that the gcd of the numerator and denominator
 * is 1.  (This is referred to as referred to as canonical form in GMP's
 * literature.) A consequence is that that the numerator and denominator may be
 * different than the values used to construct the Rational.
 *
 * Rationals whose numerator and denominator fit into an int64_t are stored
 * inline, without a GMP object, so that creating, copying and computing with
 * them does not allocate; other rationals are stored in a GMP rational. Every
 * operation produces the inline form when the result fits; getValue() may
 * convert an inline rational to the GMP form in place, so comparisons and
 * hashing work on the value, independently of the form.
 *
 * NOTE: The correct way to create a Rational from an int is to use one of the
 * int numerator/int denominator constructors with the denominator 1.  Trying
 * to construct a Rational with a single int, e.g., Rational(0), will put you
 * in danger of invoking the char* constructor, from whence you will segfault.
 */

class Rational
{
 public:
  /**
   * Constructs a Rational from a mpz_class object.
   */
  Rational(const mpz_class& val)
  {
    int64_t n;
    if (gmpz_get_int64(val.get_mpz_t(), &n))
    {
      setSmall(n, 1);
    }
    else
    {
      initBig(new mpq_class(val));
    }
  }
  /**
   * Constructs a Rational from a mpq_class object.
   * Does a deep copy.
   * Assumes that the value is in canonical form, and thus does not
   * have to call canonicalize() on the value.
   */
  Rational(const mpq_class& val) { setMpq(val); }
  Rational(mpq_class&& val) { setMpq(std::move(val)); }

  /**
   * Creates a rational from a decimal string (e.g., <code>"1.5"</code>).
   *
   * @param dec a string encoding a decimal number in the format
   * <code>[0-9]*\.[0-9]*</code>
   */
  static Rational fromDecimal(const std::string& dec);

  /** Constructs a rational with the value 0/1. */
  Rational() { setSmall(0, 1); }
  /**
   * Constructs a Rational from a C string in a given base (defaults to 10).
   *
   * Throws std::invalid_argument if the string is not a valid rational.
   * For more information about what is a valid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  explicit Rational(const char* s, unsigned base = 10);
  Rational(const std::string& s, unsigned base = 10);

  /**
   * Creates a Rational from another Rational, q, by performing a deep copy.
   */
  Rational(const Rational& q) : d_num(q.d_num), d_den(q.d_den)
  {
    if (!isSmallRep())
    {
      initBig(new mpq_class(q.bigRef()));
    }
  }
  Rational(Rational&& q) noexcept : d_num(q.d_num), d_den(q.d_den)
  {
    q.d_num = 0;
    q.d_den = 1;
  }

  /**
   * Constructs a canonical Rational from a numerator.
   */
  Rational(signed int n) { setSmall(n, 1); }
  Rational(unsigned int n) { setSmall(n, 1); }
  Rational(signed long int n) { setSmall(n, 1); }
  Rational(unsigned long int n) { setParts(n, 1); }

#ifdef CVC5_NEED_INT64_T_OVERLOADS
  Rational(int64_t n) { setSmall(n, 1); }
  Rational(uint64_t n) { setParts(n, 1); }
#endif /* CVC5_NEED_INT64_T_OVERLOADS */

  /**
   * Constructs a canonical Rational from a numerator and denominator.
   */
  Rational(signed int n, signed int d) { setParts(n, d); }
  Rational(unsigned int n, unsigned int d) { setParts(n, d); }
  Rational(signed long int n, signed long int d) { setParts(n, d); }
  Rational(unsigned long int n, unsigned long int d) { setParts(n, d); }

#ifdef CVC5_NEED_INT64_T_OVERLOADS
  Rational(int64_t n, int64_t d) { setParts(n, d); }
  Rational(uint64_t n, uint64_t d) { setParts(n, d); }
#endif /* CVC5_NEED_INT64_T_OVERLOADS */

  Rational(const Integer& n, const Integer& d);
  Rational(const Integer& n)
  {
    if (n.isSmallRep())
    {
      setSmall(n.smallVal(), 1);
    }
    else
    {
      initBig(new mpq_class(n.bigRef()));
      setMpqCanonical();
    }
  }
  ~Rational()
  {
    if (!isSmallRep())
    {
      delete &bigRef();
    }
  }

  /**
   * Returns a reference to the value as a GMP rational, for public access of
   * GMP data. Converts an inline rational to the GMP form.
   */
  const mpq_class& getValue() const
  {
    if (isSmallRep())
    {
      const_cast<Rational*>(this)->promote();
    }
    return bigRef();
  }

  /**
   * Returns the value of numerator of the Rational.
   * Note that this makes a deep copy of the numerator.
   */
  Integer getNumerator() const
  {
    return isSmallRep() ? Integer(d_num) : Integer(bigRef().get_num());
  }

  /**
   * Returns the value of denominator of the Rational.
   * Note that this makes a deep copy of the denominator.
   */
  Integer getDenominator() const
  {
    return isSmallRep() ? Integer(d_den) : Integer(bigRef().get_den());
  }

  /** Return an exact rational for a double d. */
  static std::optional<Rational> fromDouble(double d);

  /**
   * Get a double representation of this Rational, which is
   * approximate: truncation may occur, overflow may result in
   * infinity, and underflow may result in zero.
   */
  double getDouble() const;

  Rational inverse() const
  {
    return Rational(getDenominator(), getNumerator());
  }

  int cmp(const Rational& x) const
  {
    if (bothSmall(x))
    {
      if (d_den == x.d_den)
      {
        return (d_num > x.d_num) - (d_num < x.d_num);
      }
      __int128 a = static_cast<__int128>(d_num) * x.d_den;
      __int128 b = static_cast<__int128>(x.d_num) * d_den;
      return (a > b) - (a < b);
    }
    return cmpSlow(x);
  }

  int sgn() const
  {
    return isSmallRep() ? (d_num > 0) - (d_num < 0)
                        : mpq_sgn(bigRef().get_mpq_t());
  }

  bool isZero() const { return sgn() == 0; }

  bool isOne() const
  {
    return isSmallRep() ? d_num == 1 && d_den == 1
                        : mpq_cmp_si(bigRef().get_mpq_t(), 1, 1) == 0;
  }

  bool isNegativeOne() const
  {
    return isSmallRep() ? d_num == -1 && d_den == 1
                        : mpq_cmp_si(bigRef().get_mpq_t(), -1, 1) == 0;
  }

  Rational abs() const
  {
    if (sgn() < 0)
    {
      return -(*this);
    }
    else
    {
      return *this;
    }
  }

  Integer floor() const;
  Integer ceiling() const;

  Rational floor_frac() const { return (*this) - Rational(floor()); }

  Rational& operator=(const Rational& x)
  {
    if (this == &x)
    {
      return *this;
    }
    if (x.isSmallRep())
    {
      setSmallCanonical(x.d_num, x.d_den);
    }
    else if (isSmallRep())
    {
      initBig(new mpq_class(x.bigRef()));
    }
    else
    {
      bigRef() = x.bigRef();
    }
    return *this;
  }
  Rational& operator=(Rational&& x) noexcept
  {
    std::swap(d_num, x.d_num);
    std::swap(d_den, x.d_den);
    return *this;
  }

  Rational operator-() const
  {
    if (isSmallRep() && d_num != std::numeric_limits<int64_t>::min())
    {
      Rational r;
      r.d_num = -d_num;
      r.d_den = d_den;
      return r;
    }
    return negSlow();
  }

  bool operator==(const Rational& y) const
  {
    return bothSmall(y) ? d_num == y.d_num && d_den == y.d_den
                        : cmpSlow(y) == 0;
  }

  bool operator!=(const Rational& y) const { return !(*this == y); }

  bool operator<(const Rational& y) const { return cmp(y) < 0; }

  bool operator<=(const Rational& y) const { return cmp(y) <= 0; }

  bool operator>(const Rational& y) const { return cmp(y) > 0; }

  bool operator>=(const Rational& y) const { return cmp(y) >= 0; }

  Rational operator+(const Rational& y) const
  {
    if (bothSmall(y) && d_den == 1 && y.d_den == 1)
    {
      int64_t r;
      if (!__builtin_add_overflow(d_num, y.d_num, &r))
      {
        Rational q;
        q.d_num = r;
        return q;
      }
    }
    return addSlow(y, false);
  }
  Rational operator-(const Rational& y) const
  {
    if (bothSmall(y) && d_den == 1 && y.d_den == 1)
    {
      int64_t r;
      if (!__builtin_sub_overflow(d_num, y.d_num, &r))
      {
        Rational q;
        q.d_num = r;
        return q;
      }
    }
    return addSlow(y, true);
  }
  Rational operator*(const Rational& y) const
  {
    if (bothSmall(y) && d_den == 1 && y.d_den == 1)
    {
      int64_t r;
      if (!__builtin_mul_overflow(d_num, y.d_num, &r))
      {
        Rational q;
        q.d_num = r;
        return q;
      }
    }
    return mulSlow(y);
  }
  Rational operator/(const Rational& y) const { return divSlow(y); }

  Rational& operator+=(const Rational& y) { return *this = *this + y; }
  Rational& operator-=(const Rational& y) { return *this = *this - y; }
  Rational& operator*=(const Rational& y) { return *this = *this * y; }
  Rational& operator/=(const Rational& y) { return *this = *this / y; }

  bool isIntegral() const
  {
    return isSmallRep() ? d_den == 1
                        : mpz_cmp_ui(bigRef().get_den_mpz_t(), 1) == 0;
  }

  /** Returns a string representing the rational in the given base. */
  std::string toString(int base = 10) const;

  /**
   * Computes the hash of the rational from hashes of the numerator and the
   * denominator.
   */
  size_t hash() const
  {
    // the same value as with gmpz_hash() of the numerator and denominator of
    // the GMP form
    return isSmallRep() ? gmpz_hash_u64(Integer::absU64(d_num))
                              ^ gmpz_hash_u64(static_cast<uint64_t>(d_den))
                        : hashSlow();
  }

  uint32_t complexity() const
  {
    uint32_t numLen = getNumerator().length();
    uint32_t denLen = getDenominator().length();
    return numLen + denLen;
  }

  /** Equivalent to calling (this->abs()).cmp(b.abs()) */
  int absCmp(const Rational& q) const;

 private:
  bool bothSmall(const Rational& y) const
  {
    return isSmallRep() && y.isSmallRep();
  }
  /** Sets the value to n/d, which must be canonical, in the inline form. */
  void setSmallCanonical(int64_t n, int64_t d)
  {
    if (!isSmallRep())
    {
      delete &bigRef();
    }
    d_num = n;
    d_den = d;
  }
  /** Initializes the value to n/d, which must be canonical, inline. */
  void setSmall(int64_t n, int64_t d)
  {
    d_num = n;
    d_den = d;
  }
  /** Initializes the value to the canonical form of n/d. */
  void setParts(__int128 n, __int128 d);
  /** Initializes the value to that of x, in the inline form if possible. */
  void setMpq(const mpq_class& x);
  void setMpq(mpq_class&& x);
  /** Canonicalizes bigRef(), then uses the inline form if it fits. */
  void setMpqCanonical();
  /** Converts an inline rational to the GMP form, keeping its value. */
  void promote();
  /**
   * Returns a read-only GMP view of the value, without allocating; see
   * Integer::mpzView.
   */
  mpq_srcptr mpqView(
      mpq_t tmp, mpz_t tn, mpz_t td, mp_limb_t* ln, mp_limb_t* ld) const;
  /** The Rational n/d, where d > 0 and n/d is canonical. */
  static Rational fromCanonical(__int128 n, __int128 d);
  /**
   * The product of the canonical rationals an/ad and bn/bd, where |an|, ad,
   * |bn|, bd are at most 2^63.
   */
  static Rational mulParts(__int128 an, uint64_t ad, __int128 bn, uint64_t bd);
  /** Out-of-line implementations for the general case. */
  int cmpSlow(const Rational& y) const;
  Rational negSlow() const;
  Rational addSlow(const Rational& y, bool subtract) const;
  Rational mulSlow(const Rational& y) const;
  Rational divSlow(const Rational& y) const;
  size_t hashSlow() const;

  bool isSmallRep() const { return d_den != 0; }
  mpq_class& bigRef() const
  {
    return *reinterpret_cast<mpq_class*>(static_cast<intptr_t>(d_num));
  }
  /** Initializes the value to the heap-allocated GMP rational p. */
  void initBig(mpq_class* p)
  {
    d_num = static_cast<int64_t>(reinterpret_cast<intptr_t>(p));
    d_den = 0;
  }

  /**
   * The value: if d_den != 0, the canonical rational d_num / d_den (with
   * d_den > 0); otherwise d_num holds a pointer to a heap-allocated GMP
   * rational.
   */
  int64_t d_num;
  int64_t d_den;
}; /* class Rational */

struct RationalHashFunction
{
  inline size_t operator()(const cvc5::internal::Rational& r) const
  {
    return r.hash();
  }
}; /* struct RationalHashFunction */

std::ostream& operator<<(std::ostream& os, const Rational& n);

}  // namespace cvc5::internal

#endif /* CVC5__RATIONAL_H */
