/*********************                                                        */
/*! \file rational_gmp_imp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Gereon Kremer, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Multiprecision rational constants; wraps a GMP multiprecision
 ** rational.
 **
 ** Multiprecision rational constants; wraps a GMP multiprecision rational.
 **/

#include "cvc4_public.h"

#ifndef CVC4__RATIONAL_H
#define CVC4__RATIONAL_H

/*
 * Older versions of GMP in combination with newer versions of GCC and C++11
 * cause errors: https://gcc.gnu.org/gcc-4.9/porting_to.html
 * Including <cstddef> is a workaround for this issue.
 */
#include <gmp.h>

#include <cstddef>
#include <string>

#include "base/exception.h"
#include "util/integer.h"
#include "util/maybe.h"

namespace CVC4 {

/**
 ** A multi-precision rational constant.
 ** This stores the rational as a pair of multi-precision integers,
 ** one for the numerator and one for the denominator.
 ** The number is always stored so that the gcd of the numerator and denominator
 ** is 1.  (This is referred to as referred to as canonical form in GMP's
 ** literature.) A consequence is that that the numerator and denominator may be
 ** different than the values used to construct the Rational.
 **
 ** NOTE: The correct way to create a Rational from an int is to use one of the
 ** int numerator/int denominator constructors with the denominator 1.  Trying
 ** to construct a Rational with a single int, e.g., Rational(0), will put you
 ** in danger of invoking the char* constructor, from whence you will segfault.
 **/

class CVC4_PUBLIC Rational
{
 public:
  /**
   * Constructs a Rational from a mpq_class object.
   * Does a deep copy.
   * Assumes that the value is in canonical form, and thus does not
   * have to call canonicalize() on the value.
   */
  Rational(const mpq_class& val) : d_value(val) {}

  /**
   * Creates a rational from a decimal string (e.g., <code>"1.5"</code>).
   *
   * @param dec a string encoding a decimal number in the format
   * <code>[0-9]*\.[0-9]*</code>
   */
  static Rational fromDecimal(const std::string& dec);

  /** Constructs a rational with the value 0/1. */
  Rational() : d_value(0) { d_value.canonicalize(); }

  /**
   * Constructs a Rational from a C string in a given base (defaults to 10).
   *
   * Throws std::invalid_argument if the string is not a valid rational.
   * For more information about what is a valid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  explicit Rational(const char* s, unsigned base = 10) : d_value(s, base)
  {
    d_value.canonicalize();
  }
  Rational(const std::string& s, unsigned base = 10) : d_value(s, base)
  {
    d_value.canonicalize();
  }

  /**
   * Creates a Rational from another Rational, q, by performing a deep copy.
   */
  Rational(const Rational& q) : d_value(q.d_value) { d_value.canonicalize(); }

  /**
   * Constructs a canonical Rational from a numerator.
   */
  Rational(signed int n) : d_value(n, 1) { d_value.canonicalize(); }
  Rational(unsigned int n) : d_value(n, 1) { d_value.canonicalize(); }
  Rational(signed long int n) : d_value(n, 1) { d_value.canonicalize(); }
  Rational(unsigned long int n) : d_value(n, 1) { d_value.canonicalize(); }

#ifdef CVC4_NEED_INT64_T_OVERLOADS
  Rational(int64_t n) : d_value(static_cast<long>(n), 1)
  {
    d_value.canonicalize();
  }
  Rational(uint64_t n) : d_value(static_cast<unsigned long>(n), 1)
  {
    d_value.canonicalize();
  }
#endif /* CVC4_NEED_INT64_T_OVERLOADS */

  /**
   * Constructs a canonical Rational from a numerator and denominator.
   */
  Rational(signed int n, signed int d) : d_value(n, d)
  {
    d_value.canonicalize();
  }
  Rational(unsigned int n, unsigned int d) : d_value(n, d)
  {
    d_value.canonicalize();
  }
  Rational(signed long int n, signed long int d) : d_value(n, d)
  {
    d_value.canonicalize();
  }
  Rational(unsigned long int n, unsigned long int d) : d_value(n, d)
  {
    d_value.canonicalize();
  }

#ifdef CVC4_NEED_INT64_T_OVERLOADS
  Rational(int64_t n, int64_t d)
      : d_value(static_cast<long>(n), static_cast<long>(d))
  {
    d_value.canonicalize();
  }
  Rational(uint64_t n, uint64_t d)
      : d_value(static_cast<unsigned long>(n), static_cast<unsigned long>(d))
  {
    d_value.canonicalize();
  }
#endif /* CVC4_NEED_INT64_T_OVERLOADS */

  Rational(const Integer& n, const Integer& d)
      : d_value(n.get_mpz(), d.get_mpz())
  {
    d_value.canonicalize();
  }
  Rational(const Integer& n) : d_value(n.get_mpz()) { d_value.canonicalize(); }
  ~Rational() {}

  /**
   * Returns a copy of d_value to enable public access of GMP data.
   */
  const mpq_class& getValue() const { return d_value; }

  /**
   * Returns the value of numerator of the Rational.
   * Note that this makes a deep copy of the numerator.
   */
  Integer getNumerator() const { return Integer(d_value.get_num()); }

  /**
   * Returns the value of denominator of the Rational.
   * Note that this makes a deep copy of the denominator.
   */
  Integer getDenominator() const { return Integer(d_value.get_den()); }

  static Maybe<Rational> fromDouble(double d);

  /**
   * Get a double representation of this Rational, which is
   * approximate: truncation may occur, overflow may result in
   * infinity, and underflow may result in zero.
   */
  double getDouble() const { return d_value.get_d(); }

  Rational inverse() const
  {
    return Rational(getDenominator(), getNumerator());
  }

  int cmp(const Rational& x) const
  {
    // Don't use mpq_class's cmp() function.
    // The name ends up conflicting with this function.
    return mpq_cmp(d_value.get_mpq_t(), x.d_value.get_mpq_t());
  }

  int sgn() const { return mpq_sgn(d_value.get_mpq_t()); }

  bool isZero() const { return sgn() == 0; }

  bool isOne() const { return mpq_cmp_si(d_value.get_mpq_t(), 1, 1) == 0; }

  bool isNegativeOne() const
  {
    return mpq_cmp_si(d_value.get_mpq_t(), -1, 1) == 0;
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

  Integer floor() const
  {
    mpz_class q;
    mpz_fdiv_q(q.get_mpz_t(), d_value.get_num_mpz_t(), d_value.get_den_mpz_t());
    return Integer(q);
  }

  Integer ceiling() const
  {
    mpz_class q;
    mpz_cdiv_q(q.get_mpz_t(), d_value.get_num_mpz_t(), d_value.get_den_mpz_t());
    return Integer(q);
  }

  Rational floor_frac() const { return (*this) - Rational(floor()); }

  Rational& operator=(const Rational& x)
  {
    if (this == &x) return *this;
    d_value = x.d_value;
    return *this;
  }

  Rational operator-() const { return Rational(-(d_value)); }

  bool operator==(const Rational& y) const { return d_value == y.d_value; }

  bool operator!=(const Rational& y) const { return d_value != y.d_value; }

  bool operator<(const Rational& y) const { return d_value < y.d_value; }

  bool operator<=(const Rational& y) const { return d_value <= y.d_value; }

  bool operator>(const Rational& y) const { return d_value > y.d_value; }

  bool operator>=(const Rational& y) const { return d_value >= y.d_value; }

  Rational operator+(const Rational& y) const
  {
    return Rational(d_value + y.d_value);
  }
  Rational operator-(const Rational& y) const
  {
    return Rational(d_value - y.d_value);
  }

  Rational operator*(const Rational& y) const
  {
    return Rational(d_value * y.d_value);
  }
  Rational operator/(const Rational& y) const
  {
    return Rational(d_value / y.d_value);
  }

  Rational& operator+=(const Rational& y)
  {
    d_value += y.d_value;
    return (*this);
  }
  Rational& operator-=(const Rational& y)
  {
    d_value -= y.d_value;
    return (*this);
  }

  Rational& operator*=(const Rational& y)
  {
    d_value *= y.d_value;
    return (*this);
  }

  Rational& operator/=(const Rational& y)
  {
    d_value /= y.d_value;
    return (*this);
  }

  bool isIntegral() const { return getDenominator() == 1; }

  /** Returns a string representing the rational in the given base. */
  std::string toString(int base = 10) const { return d_value.get_str(base); }

  /**
   * Computes the hash of the rational from hashes of the numerator and the
   * denominator.
   */
  size_t hash() const
  {
    size_t numeratorHash = gmpz_hash(d_value.get_num_mpz_t());
    size_t denominatorHash = gmpz_hash(d_value.get_den_mpz_t());

    return numeratorHash xor denominatorHash;
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
  /**
   * Stores the value of the rational is stored in a C++ GMP rational class.
   * Using this instead of mpq_t allows for easier destruction.
   */
  mpq_class d_value;

}; /* class Rational */

struct RationalHashFunction
{
  inline size_t operator()(const CVC4::Rational& r) const { return r.hash(); }
}; /* struct RationalHashFunction */

CVC4_PUBLIC std::ostream& operator<<(std::ostream& os, const Rational& n);

}  // namespace CVC4

#endif /* CVC4__RATIONAL_H */
