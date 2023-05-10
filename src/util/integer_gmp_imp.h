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
 * A multiprecision integer constant; wraps a GMP multiprecision integer.
 */

#include "cvc5_public.h"

#ifndef CVC5__INTEGER_H
#define CVC5__INTEGER_H

#include <gmpxx.h>

#include <iosfwd>
#include <string>

namespace cvc5::internal {

class Rational;

class Integer
{
  friend class cvc5::internal::Rational;

 public:
  /**
   * Constructs an Integer by copying a GMP C++ primitive.
   */
  Integer(const mpz_class& val) : d_value(val) {}

  /** Constructs a rational with the value 0. */
  Integer() : d_value(0) {}

  /**
   * Constructs a Integer from a C string.
   * Throws std::invalid_argument if the string is not a valid rational.
   * For more information about what is a valid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  explicit Integer(const char* s, unsigned base = 10);
  explicit Integer(const std::string& s, unsigned base = 10);

  Integer(const Integer& q) : d_value(q.d_value) {}

  Integer(signed int z) : d_value(z) {}
  Integer(unsigned int z) : d_value(z) {}
  Integer(signed long int z) : d_value(z) {}
  Integer(unsigned long int z) : d_value(z) {}

#ifdef CVC5_NEED_INT64_T_OVERLOADS
  Integer(int64_t z);
  Integer(uint64_t z);
#endif /* CVC5_NEED_INT64_T_OVERLOADS */

  /** Destructor. */
  ~Integer() {}

  /** Returns a copy of d_value to enable public access of GMP data. */
  const mpz_class& getValue() const { return d_value; }

  /** Overload copy assignment operator. */
  Integer& operator=(const Integer& x);

  /** Overload equality comparison operator. */
  bool operator==(const Integer& y) const;
  /** Overload disequality comparison operator. */
  bool operator!=(const Integer& y) const;
  /** Overload less than comparison operator. */
  bool operator<(const Integer& y) const;
  /** Overload less than or equal comparison operator. */
  bool operator<=(const Integer& y) const;
  /** Overload greater than comparison operator. */
  bool operator>(const Integer& y) const;
  /** Overload greater than or equal comparison operator. */
  bool operator>=(const Integer& y) const;

  /** Overload negation operator. */
  Integer operator-() const;
  /** Overload addition operator. */
  Integer operator+(const Integer& y) const;
  /** Overload addition assignment operator. */
  Integer& operator+=(const Integer& y);
  /** Overload subtraction operator. */
  Integer operator-(const Integer& y) const;
  /** Overload subtraction assignment operator. */
  Integer& operator-=(const Integer& y);
  /** Overload multiplication operator. */
  Integer operator*(const Integer& y) const;
  /** Overload multiplication assignment operator. */
  Integer& operator*=(const Integer& y);

  /** Return the bit-wise or of this and the given Integer. */
  Integer bitwiseOr(const Integer& y) const;
  /** Return the bit-wise and of this and the given Integer. */
  Integer bitwiseAnd(const Integer& y) const;
  /** Return the bit-wise exclusive or of this and the given Integer. */
  Integer bitwiseXor(const Integer& y) const;
  /** Return the bit-wise not of this Integer. */
  Integer bitwiseNot() const;

  /** Return this*(2^pow). */
  Integer multiplyByPow2(uint32_t pow) const;

  /** Set the ith bit of the current Integer to 'value'.  */
  void setBit(uint32_t i, bool value);

  /** Return true if bit at index 'i' is 1, and false otherwise. */
  bool isBitSet(uint32_t i) const;

  /**
   * Returns the integer with the binary representation of 'size' bits
   * extended with 'amount' 1's.
   */
  Integer oneExtend(uint32_t size, uint32_t amount) const;

  /** Return a 32 bit unsigned integer representation of this Integer. */
  uint32_t toUnsignedInt() const;

  /**
   * Extract a range of bits from index 'low' to (excluding) 'low + bitCount'.
   * Note: corresponds to the extract operator of theory BV.
   */
  Integer extractBitRange(uint32_t bitCount, uint32_t low) const;

  /** Returns the floor(this / y) */
  Integer floorDivideQuotient(const Integer& y) const;

  /** Returns r == this - floor(this/y)*y */
  Integer floorDivideRemainder(const Integer& y) const;

  /** Computes a floor quotient and remainder for x divided by y.  */
  static void floorQR(Integer& q,
                      Integer& r,
                      const Integer& x,
                      const Integer& y);

  /** Returns the ceil(this / y). */
  Integer ceilingDivideQuotient(const Integer& y) const;

  /** Returns the ceil(this / y). */
  Integer ceilingDivideRemainder(const Integer& y) const;

  /**
   * Computes a quotient and remainder according to Boute's Euclidean
   * definition. euclidianDivideQuotient, euclidianDivideRemainder.
   *
   * Boute, Raymond T. (April 1992).
   * The Euclidean definition of the functions div and mod.
   * ACM Transactions on Programming Languages and Systems (TOPLAS)
   * ACM Press. 14 (2): 127 - 144. doi:10.1145/128861.128862.
   */
  static void euclidianQR(Integer& q,
                          Integer& r,
                          const Integer& x,
                          const Integer& y);

  /**
   * Returns the quotient according to Boute's Euclidean definition.
   * See the documentation for euclidianQR.
   */
  Integer euclidianDivideQuotient(const Integer& y) const;

  /**
   * Returns the remainder according to Boute's Euclidean definition.
   * See the documentation for euclidianQR.
   */
  Integer euclidianDivideRemainder(const Integer& y) const;

  /** If y divides *this, then exactQuotient returns (this/y). */
  Integer exactQuotient(const Integer& y) const;

  /** Returns y mod 2^exp. */
  Integer modByPow2(uint32_t exp) const;

  /** Returns y / 2^exp. */
  Integer divByPow2(uint32_t exp) const;

  /** Return 1 if this is > 0, 0 if it is 0, and -1 if it is < 0. */
  int sgn() const;

  /** Return true if this is > 0. */
  bool strictlyPositive() const;

  /** Return true if this is < 0. */
  bool strictlyNegative() const;

  /** Return true if this is 0. */
  bool isZero() const;

  /** Return true if this is 1. */
  bool isOne() const;

  /** Return true if this is -1. */
  bool isNegativeOne() const;

  /** Raise this Integer to the power 'exp'. */
  Integer pow(uint32_t exp) const;

  /** Return the greatest common divisor of this integer with another. */
  Integer gcd(const Integer& y) const;

  /** Return the least common multiple of this integer with another. */
  Integer lcm(const Integer& y) const;

  /** Compute addition of this Integer x + y modulo m. */
  Integer modAdd(const Integer& y, const Integer& m) const;

  /** Compute multiplication of this Integer x * y modulo m. */
  Integer modMultiply(const Integer& y, const Integer& m) const;

  /**
   * Compute modular inverse x^-1 of this Integer x modulo m with m > 0.
   * Returns a value x^-1 with 0 <= x^-1 < m such that x * x^-1 = 1 modulo m
   * if such an inverse exists, and -1 otherwise.
   *
   * Such an inverse only exists if
   *   - x is non-zero
   *   - x and m are coprime, i.e., if gcd (x, m) = 1
   *
   * Note that if x and m are coprime, then x^-1 > 0 if m > 1 and x^-1 = 0
   * if m = 1 (the zero ring).
   */
  Integer modInverse(const Integer& m) const;

  /**
   * Return true if 'y' divides this integer.
   * Note: All non-zero integers devide zero, and zero does not divide zero.
   */
  bool divides(const Integer& y) const;

  /** Return the absolute value of this integer.  */
  Integer abs() const;

  /** Return a string representation of this Integer. */
  std::string toString(int base = 10) const;

  /** Return true if this Integer fits into a signed int. */
  bool fitsSignedInt() const;

  /** Return true if this Integer fits into an unsigned int. */
  bool fitsUnsignedInt() const;

  /** Return the signed int representation of this Integer. */
  signed int getSignedInt() const;

  /** Return the unsigned int representation of this Integer. */
  unsigned int getUnsignedInt() const;

  /** Return the signed long representation of this Integer. */
  long getLong() const;

  /** Return the unsigned long representation of this Integer. */
  unsigned long getUnsignedLong() const;

  /** Return the int64_t representation of this Integer. */
  int64_t getSigned64() const;

  /** Return the uint64_t representation of this Integer. */
  uint64_t getUnsigned64() const;

  /**
   * Computes the hash of the node from the first word of the
   * numerator, the denominator.
   */
  size_t hash() const;

  /**
   * Returns true iff bit n is set.
   *
   * @param n the bit to test (0 == least significant bit)
   * @return true if bit n is set in this integer; false otherwise
   */
  bool testBit(unsigned n) const;

  /**
   * Returns k if the integer is equal to 2^(k-1)
   * @return k if the integer is equal to 2^(k-1) and 0 otherwise
   */
  unsigned isPow2() const;

  /**
   * If x != 0, returns the smallest n s.t. 2^{n-1} <= abs(x) < 2^{n}.
   * If x == 0, returns 1.
   */
  size_t length() const;

  /**
   * Returns whether `x` is probably a prime.
   *
   * A false result is always accurate, but a true result may be inaccurate
   * with small (approximately 2^{-60}) probability.
   */
  bool isProbablePrime() const;

  /**
   * Return the greatest common divisor of a and b, and in addition set s and t
   * to coefficients satisfying a*s + b*t = g.
   *
   * Note: The returned Integer is always positive, even if one or both of a
   *       and b are negative (or zero if both inputs are zero). For more
   *       details, see https://gmplib.org/manual/Number-Theoretic-Functions.
   */
  static void extendedGcd(
      Integer& g, Integer& s, Integer& t, const Integer& a, const Integer& b);

  /** Returns a reference to the minimum of two integers. */
  static const Integer& min(const Integer& a, const Integer& b);

  /** Returns a reference to the maximum of two integers. */
  static const Integer& max(const Integer& a, const Integer& b);

 private:
  /**
   * Gets a reference to the gmp data that backs up the integer.
   * Only accessible to friend classes.
   */
  const mpz_class& get_mpz() const { return d_value; }

  /**
   * The value of the rational is stored in a C++ GMP integer class.
   * Using this instead of mpz_t allows for easier destruction.
   */
  mpz_class d_value;
}; /* class Integer */

struct IntegerHashFunction
{
  inline size_t operator()(const cvc5::internal::Integer& i) const { return i.hash(); }
}; /* struct IntegerHashFunction */

inline std::ostream& operator<<(std::ostream& os, const Integer& n)
{
  return os << n.toString();
}

}  // namespace cvc5::internal

#endif /* CVC5__INTEGER_H */
