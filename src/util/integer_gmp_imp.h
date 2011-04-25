/*********************                                                        */
/*! \file integer_gmp_imp.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): dejan, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

class Integer {
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

  Integer operator/(const Integer& y) const {
    return Integer( d_value / y.d_value );
  }
  Integer& operator/=(const Integer& y) {
    d_value /= y.d_value;
    return *this;
  }

  Integer operator%(const Integer& y) const {
    return Integer( d_value % y.d_value );
  }
  Integer& operator%=(const Integer& y) {
    d_value %= y.d_value;
    return *this;
  }

  /** Raise this Integer to the power <code>exp</code>.
   *
   * @param exp the exponent
   */
  Integer pow(unsigned long int exp) const {
    mpz_class result;
    mpz_pow_ui(result.get_mpz_t(),d_value.get_mpz_t(),exp);
    return Integer( result );
  }

  std::string toString(int base = 10) const{
    return d_value.get_str(base);
  }

  //friend std::ostream& operator<<(std::ostream& os, const Integer& n);

  long getLong() const {
    long si = d_value.get_si();
#ifdef CVC4_ASSERTIONS
    // ensure there wasn't overflow
    Assert(mpz_cmp_si(d_value.get_mpz_t(), si) == 0);
#endif /* CVC4_ASSERTIONS */
    return si;
  }
  unsigned long getUnsignedLong() const {
    unsigned long ui = d_value.get_ui();
#ifdef CVC4_ASSERTIONS
    // ensure there wasn't overflow
    Assert(mpz_cmp_ui(d_value.get_mpz_t(), ui) == 0);
#endif /* CVC4_ASSERTIONS */
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
