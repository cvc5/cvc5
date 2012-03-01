/*********************                                                        */
/*! \file integer_gmp_imp.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: mdeters
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief A multiprecision integer constant; wraps a GMP multiprecision
 ** integer.
 **
 ** A multiprecision integer constant; wraps a GMP multiprecision integer.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__INTEGER_H
#define __CVC4__INTEGER_H

#include <string>
#include <iostream>

#include "util/Assert.h"
#include "util/gmp_util.h"

namespace CVC4 {

class Rational;

class CVC4_PUBLIC Integer {
private:
  /**
   * Stores the value of the rational is stored in a C++ GMP integer class.
   * Using this instead of mpz_t allows for easier destruction.
   */
  mpz_class d_value;

  /**
   * Gets a reference to the gmp data that backs up the integer.
   * Only accessible to friend classes.
   */
  const mpz_class& get_mpz() const { return d_value; }

  /**
   * Constructs an Integer by copying a GMP C++ primitive.
   */
  Integer(const mpz_class& val) : d_value(val) {}

public:

  /** Constructs a rational with the value 0. */
  Integer() : d_value(0){}

  /**
   * Constructs a Integer from a C string.
   * Throws std::invalid_argument if the string is not a valid rational.
   * For more information about what is a valid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  explicit Integer(const char * s, int base = 10): d_value(s,base) {}
  Integer(const std::string& s, unsigned base = 10) : d_value(s, base) {}

  Integer(const Integer& q) : d_value(q.d_value) {}

  Integer(  signed int z) : d_value(z) {}
  Integer(unsigned int z) : d_value(z) {}
  Integer(  signed long int z) : d_value(z) {}
  Integer(unsigned long int z) : d_value(z) {}

  ~Integer() {}


  Integer& operator=(const Integer& x){
    if(this == &x) return *this;
    d_value = x.d_value;
    return *this;
  }

  bool operator==(const Integer& y) const {
    return d_value == y.d_value;
  }

  Integer operator-() const {
    return Integer(-(d_value));
  }


  bool operator!=(const Integer& y) const {
    return d_value != y.d_value;
  }

  bool operator< (const Integer& y) const {
    return d_value < y.d_value;
  }

  bool operator<=(const Integer& y) const {
    return d_value <= y.d_value;
  }

  bool operator> (const Integer& y) const {
    return d_value > y.d_value;
  }

  bool operator>=(const Integer& y) const {
    return d_value >= y.d_value;
  }


  Integer operator+(const Integer& y) const {
    return Integer( d_value + y.d_value );
  }
  Integer& operator+=(const Integer& y) {
    d_value += y.d_value;
    return *this;
  }

  Integer operator-(const Integer& y) const {
    return Integer( d_value - y.d_value );
  }
  Integer& operator-=(const Integer& y) {
    d_value -= y.d_value;
    return *this;
  }

  Integer operator*(const Integer& y) const {
    return Integer( d_value * y.d_value );
  }
  Integer& operator*=(const Integer& y) {
    d_value *= y.d_value;
    return *this;
  }

  /**
   * Return this*(2^pow).
   */
  Integer multiplyByPow2(uint32_t pow) const{
    mpz_class result;
    mpz_mul_2exp(result.get_mpz_t(), d_value.get_mpz_t(), pow);
    return Integer( result );
  }

  /** See GMP Documentation. */
  Integer extractBitRange(uint32_t bitCount, uint32_t low) const {
    // bitCount = high-low+1
    uint32_t high = low + bitCount-1;
    //— Function: void mpz_fdiv_r_2exp (mpz_t r, mpz_t n, mp_bitcnt_t b)
    mpz_class rem, div;
    mpz_fdiv_r_2exp(rem.get_mpz_t(), d_value.get_mpz_t(), high+1);
    mpz_fdiv_q_2exp(div.get_mpz_t(), rem.get_mpz_t(), low);

    return Integer(div);
  }

  /**
   * Returns the floor(this / y)
   */
  Integer floorDivideQuotient(const Integer& y) const {
    mpz_class q;
    mpz_fdiv_q(q.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
    return Integer( q );
  }

  /**
   * Returns r == this - floor(this/y)*y
   */
  Integer floorDivideRemainder(const Integer& y) const {
    mpz_class r;
    mpz_fdiv_r(r.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
    return Integer( r );
  }

  /**
   * Computes a floor quoient and remainder for x divided by y.
   */
  static void floorQR(Integer& q, Integer& r, const Integer& x, const Integer& y) {
    mpz_fdiv_qr(q.d_value.get_mpz_t(), r.d_value.get_mpz_t(), x.d_value.get_mpz_t(), y.d_value.get_mpz_t());
  }

  /**
   * Returns the ceil(this / y)
   */
  Integer ceilingDivideQuotient(const Integer& y) const {
    mpz_class q;
    mpz_cdiv_q(q.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
    return Integer( q );
  }

  /**
   * Returns the ceil(this / y)
   */
  Integer ceilingDivideRemainder(const Integer& y) const {
    mpz_class r;
    mpz_cdiv_r(r.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
    return Integer( r );
  }

  /**
   * If y divides *this, then exactQuotient returns (this/y)
   */
  Integer exactQuotient(const Integer& y) const {
    Assert(y.divides(*this));
    mpz_class q;
    mpz_divexact(q.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
    return Integer( q );
  }

  int sgn() const {
    return mpz_sgn(d_value.get_mpz_t());
  }

  /**
   * Raise this Integer to the power <code>exp</code>.
   *
   * @param exp the exponent
   */
  Integer pow(unsigned long int exp) const {
    mpz_class result;
    mpz_pow_ui(result.get_mpz_t(),d_value.get_mpz_t(),exp);
    return Integer( result );
  }

  /**
   * Return the greatest common divisor of this integer with another.
   */
  Integer gcd(const Integer& y) const {
    mpz_class result;
    mpz_gcd(result.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
    return Integer(result);
  }

  /**
   * Return the least common multiple of this integer with another.
   */
  Integer lcm(const Integer& y) const {
    mpz_class result;
    mpz_lcm(result.get_mpz_t(), d_value.get_mpz_t(), y.d_value.get_mpz_t());
    return Integer(result);
  }

  /**
   * All non-zero integers z, z.divide(0)
   * ! zero.divides(zero)
   */
  bool divides(const Integer& y) const {
    int res = mpz_divisible_p(y.d_value.get_mpz_t(), d_value.get_mpz_t());
    return res != 0;
  }

  /**
   * Return the absolute value of this integer.
   */
  Integer abs() const {
    return d_value >= 0 ? *this : -*this;
  }

  std::string toString(int base = 10) const{
    return d_value.get_str(base);
  }

  //friend std::ostream& operator<<(std::ostream& os, const Integer& n);

  long getLong() const {
    long si = d_value.get_si();
    // ensure there wasn't overflow
    AlwaysAssert(mpz_cmp_si(d_value.get_mpz_t(), si) == 0,
                 "Overflow when extracting long from multiprecision integer");
    return si;
  }
  unsigned long getUnsignedLong() const {
    unsigned long ui = d_value.get_ui();
    // ensure there wasn't overflow
    AlwaysAssert(mpz_cmp_ui(d_value.get_mpz_t(), ui) == 0,
                 "Overflow when extracting unsigned long from multiprecision integer");
    return ui;
  }

  /**
   * Computes the hash of the node from the first word of the
   * numerator, the denominator.
   */
  size_t hash() const {
    return gmpz_hash(d_value.get_mpz_t());
  }

  /**
   * Returns true iff bit n is set.
   *
   * @param n the bit to test (0 == least significant bit)
   * @return true if bit n is set in this integer; false otherwise
   */
  bool testBit(unsigned n) const {
    return mpz_tstbit(d_value.get_mpz_t(), n);
  }

  /**
   * If x != 0, returns the smallest n s.t. 2^{n-1} <= abs(x) < 2^{n}.
   * If x == 0, returns 1.
   */
  size_t length() const {
    if(sgn() == 0){
      return 1;
    }else{
      return mpz_sizeinbase(d_value.get_mpz_t(),2);
    }
  }

  static void extendedGcd(Integer& g, Integer& s, Integer& t, const Integer& a, const Integer& b){
    //mpz_gcdext (mpz_t g, mpz_t s, mpz_t t, mpz_t a, mpz_t b);
    mpz_gcdext (g.d_value.get_mpz_t(), s.d_value.get_mpz_t(), t.d_value.get_mpz_t(), a.d_value.get_mpz_t(), b.d_value.get_mpz_t());
  }


  friend class CVC4::Rational;
};/* class Integer */

struct IntegerHashStrategy {
  static inline size_t hash(const CVC4::Integer& i) {
    return i.hash();
  }
};/* struct IntegerHashStrategy */

inline std::ostream& operator<<(std::ostream& os, const Integer& n) {
  return os << n.toString();
}

}/* CVC4 namespace */

#endif /* __CVC4__INTEGER_H */
