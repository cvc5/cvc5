/*********************                                                        */
/*! \file integer_cln_imp.h
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
 ** \brief A multiprecision integer constant; wraps a CLN multiprecision
 ** integer.
 **
 ** A multiprecision integer constant; wraps a CLN multiprecision integer.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__INTEGER_H
#define __CVC4__INTEGER_H

#include <string>
#include <sstream>
#include <iostream>

#include <cln/integer.h>
#include <cln/input.h>
#include <cln/integer_io.h>
#include <limits>

#include "util/Assert.h"

namespace CVC4 {

class Rational;

class CVC4_PUBLIC Integer {
private:
  /**
   * Stores the value of the rational is stored in a C++ GMP integer class.
   * Using this instead of mpz_t allows for easier destruction.
   */
  cln::cl_I d_value;

  /**
   * Gets a reference to the gmp data that backs up the integer.
   * Only accessible to friend classes.
   */
  //const mpz_class& get_mpz() const { return d_value; }
  const cln::cl_I& get_cl_I() const { return d_value; }

  /**
   * Constructs an Integer by copying a GMP C++ primitive.
   */
  //Integer(const mpz_class& val) : d_value(val) {}
  Integer(const cln::cl_I& val) : d_value(val) {}

public:

  /** Constructs a rational with the value 0. */
  Integer() : d_value(0){}

  /**
   * Constructs a Integer from a C string.
   * Throws std::invalid_argument if the string is not a valid rational.
   * For more information about what is a valid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  explicit Integer(const char * s, int base = 10) throw (std::invalid_argument){
    cln::cl_read_flags flags;
    flags.syntax = cln::syntax_integer;
    flags.lsyntax = cln::lsyntax_standard;
    flags.rational_base = base;
    try{
      d_value = read_integer(flags, s, NULL, NULL);
    }catch(...){
      std::stringstream ss;
      ss << "Integer() failed to parse value \"" <<s << "\" in base=" <<base;
      throw std::invalid_argument(ss.str());
    }
  }

  Integer(const std::string& s, int base = 10) throw (std::invalid_argument) {
    cln::cl_read_flags flags;
    flags.syntax = cln::syntax_integer;
    flags.lsyntax = cln::lsyntax_standard;
    flags.rational_base = base;
    try{
      d_value = read_integer(flags, s.c_str(), NULL, NULL);
    }catch(...){
      std::stringstream ss;
      ss << "Integer() failed to parse value \"" <<s << "\" in base=" <<base;
      throw std::invalid_argument(ss.str());
    }
  }

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

  Integer operator-() const{
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

  /*
  Integer operator/(const Integer& y) const {
    return Integer( cln::floor1(d_value, y.d_value) );
  }
  Integer& operator/=(const Integer& y) {
    d_value = cln::floor1(d_value, y.d_value);
    return *this;
  }

  Integer operator%(const Integer& y) const {
    return Integer( cln::floor2(d_value, y.d_value).remainder );
  }
  Integer& operator%=(const Integer& y) {
    d_value = cln::floor2(d_value, y.d_value).remainder;
    return *this;
  }
  */

  /**
   * Return this*(2^pow).
   */
  Integer multiplyByPow2(uint32_t pow) const {
    cln::cl_I ipow(pow);
    return Integer( d_value << ipow);
  }

  /** See CLN Documentation. */
  Integer extractBitRange(uint32_t bitCount, uint32_t low) const {
    cln::cl_byte range(bitCount, low);
    return Integer(cln::ldb(d_value, range));
  }

  /**
   * Returns the floor(this / y)
   */
  Integer floorDivideQuotient(const Integer& y) const {
    return Integer( cln::floor1(d_value, y.d_value) );
  }

  /**
   * Returns r == this - floor(this/y)*y
   */
  Integer floorDivideRemainder(const Integer& y) const {
    return Integer( cln::floor2(d_value, y.d_value).remainder );
  }
   /**
   * Computes a floor quoient and remainder for x divided by y.
   */
  static void floorQR(Integer& q, Integer& r, const Integer& x, const Integer& y) {
    cln::cl_I_div_t res = cln::floor2(x.d_value, y.d_value);
    q.d_value = res.quotient;
    r.d_value = res.remainder;
  }

  /**
   * Returns the ceil(this / y)
   */
  Integer ceilingDivideQuotient(const Integer& y) const {
    return Integer( cln::ceiling1(d_value, y.d_value) );
  }

  /**
   * Returns the ceil(this / y)
   */
  Integer ceilingDivideRemainder(const Integer& y) const {
    return Integer( cln::ceiling2(d_value, y.d_value).remainder );
  }

  /**
   * If y divides *this, then exactQuotient returns (this/y)
   */
  Integer exactQuotient(const Integer& y) const {
    Assert(y.divides(*this));
    return Integer( cln::exquo(d_value, y.d_value) );
  }

  /**
   * Raise this Integer to the power <code>exp</code>.
   *
   * @param exp the exponent
   */
  Integer pow(unsigned long int exp) const {
    if(exp > 0){
      cln::cl_I result= cln::expt_pos(d_value,exp);
      return Integer( result );
    }else if(exp == 0){
      return Integer( 1 );
    }else{
      Unimplemented();
    }
  }

  /**
   * Return the greatest common divisor of this integer with another.
   */
  Integer gcd(const Integer& y) const {
    cln::cl_I result = cln::gcd(d_value, y.d_value);
    return Integer(result);
  }

  /**
   * Return the least common multiple of this integer with another.
   */
  Integer lcm(const Integer& y) const {
    cln::cl_I result = cln::lcm(d_value, y.d_value);
    return Integer(result);
  }

  /**
   * Return true if *this exactly divides y.
   */
  bool divides(const Integer& y) const {
    cln::cl_I result = cln::rem(y.d_value, d_value);
    return cln::zerop(result);
  }

  /**
   * Return the absolute value of this integer.
   */
  Integer abs() const {
    return d_value >= 0 ? *this : -*this;
  }

  std::string toString(int base = 10) const{
    std::stringstream ss;
    switch(base){
    case 2:
      fprintbinary(ss,d_value);
      break;
    case 8:
      fprintoctal(ss,d_value);
      break;
    case 10:
      fprintdecimal(ss,d_value);
      break;
    case 16:
      fprinthexadecimal(ss,d_value);
      break;
    default:
      Unhandled();
      break;
    }
    std::string output = ss.str();
    for( unsigned i = 0; i <= output.length(); ++i){
      if(isalpha(output[i])){
        output.replace(i, 1, 1, tolower(output[i]));
      }
    }

    return output;
  }

  int sgn() const {
    cln::cl_I sgn = cln::signum(d_value);
    Assert(sgn == 0 || sgn == -1 || sgn == 1);
    return cln::cl_I_to_int(sgn);
  }

  //friend std::ostream& operator<<(std::ostream& os, const Integer& n);

  long getLong() const {
    // ensure there isn't overflow
    AlwaysAssert(d_value <= std::numeric_limits<long>::max(),
                 "Overflow detected in Integer::getLong()");
    AlwaysAssert(d_value >= std::numeric_limits<long>::min(),
                 "Overflow detected in Integer::getLong()");
    return cln::cl_I_to_long(d_value);
  }

  unsigned long getUnsignedLong() const {
    // ensure there isn't overflow
    AlwaysAssert(d_value <= std::numeric_limits<unsigned long>::max(),
                 "Overflow detected in Integer::getUnsignedLong()");
    AlwaysAssert(d_value >= std::numeric_limits<unsigned long>::min(),
                 "Overflow detected in Integer::getUnsignedLong()");
    return cln::cl_I_to_ulong(d_value);
  }

  /**
   * Computes the hash of the node from the first word of the
   * numerator, the denominator.
   */
  size_t hash() const {
    return equal_hashcode(d_value);
  }

  /**
   * Returns true iff bit n is set.
   *
   * @param n the bit to test (0 == least significant bit)
   * @return true if bit n is set in this integer; false otherwise
   */
  bool testBit(unsigned n) const {
    return cln::logbitp(n, d_value);
  }

  /**
   * If x != 0, returns the unique n s.t. 2^{n-1} <= abs(x) < 2^{n}.
   * If x == 0, returns 1.
   */
  size_t length() const {
    int s = sgn();
    if(s == 0){
      return 1;
    }else if(s < 0){
      return cln::integer_length(-d_value);
    }else{
      return cln::integer_length(d_value);
    }
  }

/*   cl_I xgcd (const cl_I& a, const cl_I& b, cl_I* u, cl_I* v) */
/* This function ("extended gcd") returns the greatest common divisor g of a and b and at the same time the representation of g as an integral linear combination of a and b: u and v with u*a+v*b = g, g >= 0. u and v will be normalized to be of smallest possible absolute value, in the following sense: If a and b are non-zero, and abs(a) != abs(b), u and v will satisfy the inequalities abs(u) <= abs(b)/(2*g), abs(v) <= abs(a)/(2*g). */
  static void extendedGcd(Integer& g, Integer& s, Integer& t, const Integer& a, const Integer& b){    
    g.d_value = cln::xgcd(a.d_value, b.d_value, &s.d_value, &t.d_value);
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
