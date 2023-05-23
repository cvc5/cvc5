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

#include "cvc5_public.h"

#ifndef CVC5__INTEGER_H
#define CVC5__INTEGER_H

#include <cln/integer.h>

#include <iosfwd>
#include <limits>
#include <string>

#include "base/exception.h"

namespace cln
{
  struct cl_read_flags;
}

namespace cvc5::internal {

class Rational;

class Integer
{
  friend class cvc5::internal::Rational;

 public:
  /**
   * Constructs an Integer by copying a CLN C++ primitive.
   */
  Integer(const cln::cl_I& val) : d_value(val) {}

  /** Constructs a rational with the value 0. */
  Integer() : d_value(0) {}

  /**
   * Constructs a Integer from a C string.
   * Throws std::invalid_argument if the string is not a valid integer.
   */
  explicit Integer(const char* sp, unsigned base = 10)
  {
    parseInt(std::string(sp), base);
  }

  /**
   * Constructs a Integer from a C++ string.
   * Throws std::invalid_argument if the string is not a valid integer.
   */
  explicit Integer(const std::string& s, unsigned base = 10)
  {
    parseInt(s, base);
  }

  Integer(const Integer& q) : d_value(q.d_value) {}

  Integer(signed int z) : d_value((signed long int)z) {}
  Integer(unsigned int z) : d_value((unsigned long int)z) {}
  Integer(signed long int z) : d_value(z) {}
  Integer(unsigned long int z) : d_value(z) {}

#ifdef CVC5_NEED_INT64_T_OVERLOADS
  Integer(int64_t z) : d_value(static_cast<long>(z)) {}
  Integer(uint64_t z) : d_value(static_cast<unsigned long>(z)) {}
#endif /* CVC5_NEED_INT64_T_OVERLOADS */

  /** Destructor. */
  ~Integer() {}

  /** Returns a copy of d_value to enable public access of CLN data. */
  const cln::cl_I& getValue() const { return d_value; }

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

  /** Return true if bit at index 'i' is 1, and false otherwise. */
  bool isBitSet(uint32_t i) const;

  /** Set the ith bit of the current Integer to 'value'.  */
  void setBit(uint32_t i, bool value);

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

  /** Returns the floor(this / y). */
  Integer floorDivideQuotient(const Integer& y) const;

  /** Returns r == this - floor(this/y)*y. */
  Integer floorDivideRemainder(const Integer& y) const;

  /** Computes a floor quoient and remainder for x divided by y.  */
  static void floorQR(Integer& q,
                      Integer& r,
                      const Integer& x,
                      const Integer& y);

  /** Returns the ceil(this / y). */
  Integer ceilingDivideQuotient(const Integer& y) const;

  /** Returns the ceil(this / y). */
  Integer ceilingDivideRemainder(const Integer& y) const;

  /**
   * Computes a quoitent and remainder according to Boute's Euclidean
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
   * Returns the quoitent according to Boute's Euclidean definition.
   * See the documentation for euclidianQR.
   */
  Integer euclidianDivideQuotient(const Integer& y) const;

  /**
   * Returns the remainfing according to Boute's Euclidean definition.
   * See the documentation for euclidianQR.
   */
  Integer euclidianDivideRemainder(const Integer& y) const;

  /** If y divides *this, then exactQuotient returns (this/y). */
  Integer exactQuotient(const Integer& y) const;

  /** Return y mod 2^exp. */
  Integer modByPow2(uint32_t exp) const;

  /** Returns y / 2^exp. */
  Integer divByPow2(uint32_t exp) const;

  /**
   * Raise this Integer to the power <code>exp</code>.
   *
   * @param exp the exponent
   */
  Integer pow(uint32_t exp) const;

  /** Return the greatest common divisor of this integer with another.  */
  Integer gcd(const Integer& y) const;

  /** Return the least common multiple of this integer with another.  */
  Integer lcm(const Integer& y) const;

  /** Compute addition of this Integer x + y modulo m.  */
  Integer modAdd(const Integer& y, const Integer& m) const;

  /** Compute multiplication of this Integer x * y modulo m.  */
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

  /** Return true if *this exactly divides y.  */
  bool divides(const Integer& y) const;

  /** Return the absolute value of this integer.  */
  Integer abs() const;

  /** Return a string representation of this Integer. */
  std::string toString(int base = 10) const;

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

  /** Return true if this Integer fits into a signed int. */
  bool fitsSignedInt() const;

  /** Return true if this Integer fits into an unsigned int. */
  bool fitsUnsignedInt() const;

  /** Return the signed int representation of this Integer. */
  int getSignedInt() const;

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
   * If x != 0, returns the unique n s.t. 2^{n-1} <= abs(x) < 2^{n}.
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

  /*   cl_I xgcd (const cl_I& a, const cl_I& b, cl_I* u, cl_I* v) */
  /* This function ("extended gcd") returns the greatest common divisor g of a
   * and b and at the same time the representation of g as an integral linear
   * combination of a and b: u and v with u*a+v*b = g, g >= 0. u and v will be
   * normalized to be of smallest possible absolute value, in the following
   * sense: If a and b are non-zero, and abs(a) != abs(b), u and v will satisfy
   * the inequalities abs(u) <= abs(b)/(2*g), abs(v) <= abs(a)/(2*g). */
  static void extendedGcd(
      Integer& g, Integer& s, Integer& t, const Integer& a, const Integer& b);

  /** Returns a reference to the minimum of two integers. */
  static const Integer& min(const Integer& a, const Integer& b);

  /** Returns a reference to the maximum of two integers. */
  static const Integer& max(const Integer& a, const Integer& b);

 private:
  /**
   * Gets a reference to the cln data that backs up the integer.
   * Only accessible to friend classes.
   */
  const cln::cl_I& get_cl_I() const { return d_value; }

  /**
   * Helper for parseInt.
   * Throws a std::invalid_argument on invalid input `s` for the given base.
   */
  void readInt(const cln::cl_read_flags& flags,
               const std::string& s,
               unsigned base);

  /**
   * Parse string representation of integer into this Integer.
   * Throws a std::invalid_argument on invalid inputs.
   */
  void parseInt(const std::string& s, unsigned base);

  /**
   * The following constants are to help with CLN conversion in 32 bit.
   * See http://www.ginac.de/CLN/cln.html#Conversions.
   */

  /**  2^29 - 1 */
  static signed int s_fastSignedIntMax;
  /** -2^29 */
  static signed int s_fastSignedIntMin;
  /** 2^29 - 1 */
  static unsigned int s_fastUnsignedIntMax;
  /** std::numeric_limits<signed int>::max() */
  static signed long s_slowSignedIntMax;
  /** std::numeric_limits<signed int>::min() */
  static signed long s_slowSignedIntMin;
  /** std::numeric_limits<unsigned int>::max() */
  static unsigned long s_slowUnsignedIntMax;
  /** std::numeric_limits<signed long>::min() */
  static unsigned long s_signedLongMin;
  /** std::numeric_limits<signed long>::max() */
  static unsigned long s_signedLongMax;
  /** std::numeric_limits<unsigned long>::max() */
  static unsigned long s_unsignedLongMax;

  /** Value of the rational is stored in a C++ CLN integer class. */
  cln::cl_I d_value;
}; /* class Integer */

struct IntegerHashFunction
{
  size_t operator()(const cvc5::internal::Integer& i) const { return i.hash(); }
}; /* struct IntegerHashFunction */

std::ostream& operator<<(std::ostream& os, const Integer& n);

}  // namespace cvc5::internal

#endif /* CVC5__INTEGER_H */
