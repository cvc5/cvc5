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
 *
 * Integers that fit into an int64_t are stored inline, without a GMP object,
 * so that creating, copying and computing with them does not allocate.
 * Other integers are stored in a GMP integer. Every operation produces the
 * inline form when the result fits; getValue() may convert an inline integer
 * to the GMP form in place, so comparisons and hashing work on the value,
 * independently of the form.
 */

#include "cvc5_public.h"

#ifndef CVC5__UTIL__INTEGER_GMP_H
#define CVC5__UTIL__INTEGER_GMP_H

#include <gmpxx.h>

#include <cstdint>
#include <functional>
#include <iosfwd>
#include <limits>
#include <new>
#include <string>
#include <utility>

#include "util/gmp_util.h"

namespace cvc5::internal {

class Rational;

class Integer
{
  friend class cvc5::internal::Rational;

 public:
  /**
   * Constructs an Integer by copying a GMP C++ primitive.
   */
  Integer(const mpz_class& val) { setMpz(val); }
  Integer(mpz_class&& val) { setMpz(std::move(val)); }

  /** Constructs a rational with the value 0. */
  Integer() : d_rep(1) {}

  /**
   * Constructs a Integer from a C string.
   * Throws std::invalid_argument if the string is not a valid rational.
   * For more information about what is a valid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  explicit Integer(const char* s, unsigned base = 10);
  explicit Integer(const std::string& s, unsigned base = 10);

  Integer(signed int z) { initSmall(z); }
  Integer(unsigned int z) { initSmall(z); }
  Integer(signed long int z) { initSmall(z); }
  Integer(unsigned long int z)
  {
    if (z < (uint64_t(1) << 62))
    {
      initSmall(static_cast<int64_t>(z));
    }
    else
    {
      d_rep = toRep(new mpz_class(z));
    }
  }

#ifdef CVC5_NEED_INT64_T_OVERLOADS
  Integer(int64_t z) { initSmall(z); }
  Integer(uint64_t z);
#endif /* CVC5_NEED_INT64_T_OVERLOADS */

  Integer(const Integer& x)
      : d_rep(x.isSmallRep() ? x.d_rep : toRep(new mpz_class(x.bigRef())))
  {
  }
  Integer(Integer&& x) noexcept : d_rep(x.d_rep) { x.d_rep = 1; }
  ~Integer()
  {
    if (!isSmallRep())
    {
      delete &bigRef();
    }
  }
  Integer& operator=(const Integer& x)
  {
    if (this == &x)
    {
      return *this;
    }
    if (x.isSmallRep())
    {
      if (!isSmallRep())
      {
        delete &bigRef();
      }
      d_rep = x.d_rep;
    }
    else if (isSmallRep())
    {
      d_rep = toRep(new mpz_class(x.bigRef()));
    }
    else
    {
      bigRef() = x.bigRef();
    }
    return *this;
  }
  Integer& operator=(Integer&& x) noexcept
  {
    std::swap(d_rep, x.d_rep);
    return *this;
  }

  /**
   * Returns a reference to the value as a GMP integer, for public access of
   * GMP data. Converts an inline integer to the GMP form.
   */
  const mpz_class& getValue() const
  {
    if (isSmallRep())
    {
      const_cast<Integer*>(this)->promote();
    }
    return bigRef();
  }

  /** Overload equality comparison operator. */
  bool operator==(const Integer& y) const
  {
    return bothSmall(y) ? smallVal() == y.smallVal() : cmpSlow(y) == 0;
  }
  /** Overload disequality comparison operator. */
  bool operator!=(const Integer& y) const { return !(*this == y); }
  /** Overload less than comparison operator. */
  bool operator<(const Integer& y) const
  {
    return bothSmall(y) ? smallVal() < y.smallVal() : cmpSlow(y) < 0;
  }
  /** Overload less than or equal comparison operator. */
  bool operator<=(const Integer& y) const
  {
    return bothSmall(y) ? smallVal() <= y.smallVal() : cmpSlow(y) <= 0;
  }
  /** Overload greater than comparison operator. */
  bool operator>(const Integer& y) const { return y < *this; }
  /** Overload greater than or equal comparison operator. */
  bool operator>=(const Integer& y) const { return y <= *this; }

  /** Overload negation operator. */
  Integer operator-() const
  {
    if (isSmallRep())
    {
      return Integer(-smallVal());
    }
    return negSlow();
  }
  /** Overload addition operator. */
  Integer operator+(const Integer& y) const
  {
    int64_t r;
    if (bothSmall(y) && !__builtin_add_overflow(smallVal(), y.smallVal(), &r))
    {
      return Integer(r);
    }
    return addSlow(y);
  }
  /** Overload addition assignment operator. */
  Integer& operator+=(const Integer& y)
  {
    int64_t r;
    if (bothSmall(y) && !__builtin_add_overflow(smallVal(), y.smallVal(), &r))
    {
      setSmall(r);
    }
    else
    {
      *this = addSlow(y);
    }
    return *this;
  }
  /** Overload subtraction operator. */
  Integer operator-(const Integer& y) const
  {
    int64_t r;
    if (bothSmall(y) && !__builtin_sub_overflow(smallVal(), y.smallVal(), &r))
    {
      return Integer(r);
    }
    return subSlow(y);
  }
  /** Overload subtraction assignment operator. */
  Integer& operator-=(const Integer& y)
  {
    int64_t r;
    if (bothSmall(y) && !__builtin_sub_overflow(smallVal(), y.smallVal(), &r))
    {
      setSmall(r);
    }
    else
    {
      *this = subSlow(y);
    }
    return *this;
  }
  /** Overload multiplication operator. */
  Integer operator*(const Integer& y) const
  {
    int64_t r;
    if (bothSmall(y) && !__builtin_mul_overflow(smallVal(), y.smallVal(), &r))
    {
      return Integer(r);
    }
    return mulSlow(y);
  }
  /** Overload multiplication assignment operator. */
  Integer& operator*=(const Integer& y)
  {
    int64_t r;
    if (bothSmall(y) && !__builtin_mul_overflow(smallVal(), y.smallVal(), &r))
    {
      setSmall(r);
    }
    else
    {
      *this = mulSlow(y);
    }
    return *this;
  }

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
  int sgn() const
  {
    return isSmallRep() ? (smallVal() > 0) - (smallVal() < 0)
                        : mpz_sgn(bigRef().get_mpz_t());
  }

  /** Return true if this is > 0. */
  bool strictlyPositive() const { return sgn() > 0; }

  /** Return true if this is < 0. */
  bool strictlyNegative() const { return sgn() < 0; }

  /** Return true if this is 0. */
  bool isZero() const { return sgn() == 0; }

  /** Return true if this is 1. */
  bool isOne() const
  {
    return isSmallRep() ? smallVal() == 1
                        : mpz_cmp_si(bigRef().get_mpz_t(), 1) == 0;
  }

  /** Return true if this is -1. */
  bool isNegativeOne() const
  {
    return isSmallRep() ? smallVal() == -1
                        : mpz_cmp_si(bigRef().get_mpz_t(), -1) == 0;
  }

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
  Integer abs() const { return sgn() >= 0 ? *this : -*this; }

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
  size_t hash() const
  {
    // the same value as gmpz_hash() of the GMP form
    return isSmallRep() ? gmpz_hash_u64(absU64(smallVal())) : hashSlow();
  }

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

  /**
   * Returns a uniformly random non-negative Integer in [0, 2^nbits).
   * Uses the cvc5 Random singleton.
   */
  static Integer mkRandom(uint32_t nbits);

 private:
  /** |x| as an unsigned 64-bit integer (also for the minimum int64_t). */
  static uint64_t absU64(int64_t x)
  {
    return x < 0 ? 0 - static_cast<uint64_t>(x) : static_cast<uint64_t>(x);
  }
  /** Whether x fits into the inline form (63 bits). */
  static bool fitsInline(int64_t x)
  {
    return x >= -(int64_t(1) << 62) && x < (int64_t(1) << 62);
  }
  bool isSmallRep() const { return d_rep & 1; }
  int64_t smallVal() const { return static_cast<int64_t>(d_rep) >> 1; }
  mpz_class& bigRef() const
  {
    return *reinterpret_cast<mpz_class*>(static_cast<uintptr_t>(d_rep));
  }
  static uint64_t toRep(mpz_class* p) { return reinterpret_cast<uintptr_t>(p); }
  /** A heap-allocated GMP integer with value x. */
  static mpz_class* newMpz(int64_t x)
  {
    mpz_class* p = new mpz_class();
    gmpz_set_int64(p->get_mpz_t(), x);
    return p;
  }
  bool bothSmall(const Integer& y) const
  {
    return isSmallRep() && y.isSmallRep();
  }
  /** Initializes the value to x. */
  void initSmall(int64_t x)
  {
    if (fitsInline(x))
    {
      d_rep = (static_cast<uint64_t>(x) << 1) | 1;
    }
    else
    {
      d_rep = toRep(newMpz(x));
    }
  }
  /** Sets the value to x. */
  void setSmall(int64_t x)
  {
    if (!isSmallRep())
    {
      delete &bigRef();
    }
    initSmall(x);
  }
  /** Initializes the value to that of x, in the inline form if it fits. */
  template <class T>
  void setMpz(T&& x)
  {
    int64_t v;
    if (gmpz_get_int64(x.get_mpz_t(), &v) && fitsInline(v))
    {
      initSmall(v);
    }
    else
    {
      d_rep = toRep(new mpz_class(std::forward<T>(x)));
    }
  }
  /** Converts an inline integer to the GMP form, keeping its value. */
  void promote() { d_rep = toRep(newMpz(smallVal())); }
  /**
   * Returns a read-only GMP view of the value, without allocating: for an
   * inline integer, `tmp` and the gmpz_limbs_per_u64 `limbs` are set up to
   * represent it, and the view is valid while they live.
   */
  mpz_srcptr mpzView(mpz_t tmp, mp_limb_t* limbs) const
  {
    if (!isSmallRep())
    {
      return bigRef().get_mpz_t();
    }
    gmpz_limbs_from_u64(limbs, absU64(smallVal()));
    // mpz_roinit_n ignores high zero limbs
    return mpz_roinit_n(
        tmp, limbs, smallVal() < 0 ? -gmpz_limbs_per_u64 : gmpz_limbs_per_u64);
  }
  /** Out-of-line implementations for the general case. */
  int cmpSlow(const Integer& y) const;
  Integer negSlow() const;
  Integer addSlow(const Integer& y) const;
  Integer subSlow(const Integer& y) const;
  Integer mulSlow(const Integer& y) const;
  size_t hashSlow() const;

  /**
   * The value: if the lowest bit is 1, the integer (value << 1) | 1, which
   * covers [-2^62, 2^62); otherwise a pointer to a heap-allocated GMP integer.
   */
  uint64_t d_rep;
}; /* class Integer */

inline std::ostream& operator<<(std::ostream& os, const Integer& n)
{
  return os << n.toString();
}

}  // namespace cvc5::internal

namespace std {
template <>
struct hash<cvc5::internal::Integer>
{
  size_t operator()(const cvc5::internal::Integer& i) const { return i.hash(); }
};
}  // namespace std

#endif /* CVC5__UTIL__INTEGER_GMP_H */
