/*********************                                                        */
/** rational.h
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** A multiprecision rational constant.
 **/

#include <gmpxx.h>
#include <string>
#include "integer.h"

#ifndef __CVC4__RATIONAL_H
#define __CVC4__RATIONAL_H

namespace CVC4 {

class Rational {
private:
  /**
   * Stores the value of the rational is stored in a C++ GMP rational class.
   * Using this instead of mpq_t allows for easier destruction.
   */
  mpq_class d_value;

  /**
   * Constructs a Rational from a mpq_class object.
   * Does a deep copy.
   * Assumes that the value is in canonical form, and thus does not
   * have to call canonicalize() on the value.
   */
  Rational(const mpq_class& val) : d_value(val) {  }

public:

  /** Constructs a rational with the value 0/1. */
  Rational() : d_value(0){
    d_value.canonicalize();
  }

  /**
   * Constructs a Rational from a C string.
   * Throws std::invalid_argument if the stribng is not a valid rational.
   * For more information about what is a vaid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  Rational(const char * s, int base = 10): d_value(s,base) {
    d_value.canonicalize();
  }
  Rational(const std::string& s, unsigned base = 10) : d_value(s, base) {
    d_value.canonicalize();
  }

  Rational(const Rational& q) : d_value(q.d_value) {
    d_value.canonicalize();
  }

  Rational(  signed int n,   signed int d) : d_value(n,d) {
    d_value.canonicalize();
  }
  Rational(unsigned int n, unsigned int d) : d_value(n,d) {
    d_value.canonicalize();
  }
  Rational(  signed long int n,   signed long int d) : d_value(n,d) {
    d_value.canonicalize();
  }
  Rational(unsigned long int n, unsigned long int d) : d_value(n,d) {
    d_value.canonicalize();
  }

  Rational(const Integer& n, const Integer& d):
    d_value(n.get_mpz(), d.get_mpz())
  {
    d_value.canonicalize();
  }

  ~Rational() {}


  Integer getNumerator() const {
    return Integer(d_value.get_num());
  }

  Integer getDenominator() const{
    return Integer(d_value.get_den());
  }


  Rational& operator=(const Rational& x){
    if(this == &x) return *this;
    d_value = x.d_value;
    return *this;
  }

  Rational operator-() const{
    return Rational(-(d_value));
  }

  bool operator==(const Rational& y) const {
    return d_value == y.d_value;
  }

  bool operator!=(const Rational& y) const {
    return d_value != y.d_value;
  }

  bool operator< (const Rational& y) const {
    return d_value < y.d_value;
  }

  bool operator<=(const Rational& y) const {
    return d_value <= y.d_value;
  }

  bool operator> (const Rational& y) const {
    return d_value > y.d_value;
  }

  bool operator>=(const Rational& y) const {
    return d_value >= y.d_value;
  }


  Rational operator+(const Rational& y) const{
    return Rational( d_value + y.d_value );
  }

  Rational operator-(const Rational& y) const {
    return Rational( d_value - y.d_value );
  }

  Rational operator*(const Rational& y) const {
    return Rational( d_value * y.d_value );
  }
  Rational operator/(const Rational& y) const {
    return Rational( d_value / y.d_value );
  }

  std::string toString(int base = 10) const {
    return d_value.get_str(base);
  }


  friend std::ostream& operator<<(std::ostream& os, const Rational& n);


  /**
   * Computes the hash of the node from the first word of the
   * numerator, the denominator.
   */
  size_t hash() const {
    size_t numeratorHash = gmpz_hash(d_value.get_num_mpz_t());
    size_t denominatorHash = gmpz_hash(d_value.get_den_mpz_t());

    return numeratorHash xor denominatorHash;
  }

};/* class Rational */

std::ostream& operator<<(std::ostream& os, const Rational& n);

}/* CVC4 namespace */

#endif /* __CVC4__RATIONAL_H */

