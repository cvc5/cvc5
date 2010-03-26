/*********************                                                        */
/** integer.h
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
 ** A multiprecision integer constant.
 **/
#include <gmpxx.h>
#include <string>


#ifndef __CVC4__INTEGER_H
#define __CVC4__INTEGER_H

namespace CVC4 {

/** Hashes the gmp integer primitive in a word by word fashion. */
inline size_t gmpz_hash(const mpz_t toHash){
  size_t hash = 0;
  for (int i=0, n=mpz_size(toHash); i<n; ++i){
    mp_limb_t limb = mpz_getlimbn(toHash, i);
    hash = hash * 2;
    hash = hash xor limb;
  }
  return hash;
}

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
   * Throws std::invalid_argument if the stribng is not a valid rational.
   * For more information about what is a vaid rational string,
   * see GMP's documentation for mpq_set_str().
   */
  Integer(const char * s, int base = 10): d_value(s,base) {}
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


  Integer operator+(const Integer& y) const{
    return Integer( d_value + y.d_value );
  }

  Integer operator-(const Integer& y) const {
    return Integer( d_value - y.d_value );
  }

  Integer operator*(const Integer& y) const {
    return Integer( d_value * y.d_value );
  }
  Integer operator/(const Integer& y) const {
    return Integer( d_value / y.d_value );
  }

  std::string toString(int base = 10) const{
    return d_value.get_str(base);
  }

  //friend std::ostream& operator<<(std::ostream& os, const Integer& n);

  long getLong() const { return d_value.get_si(); }
  unsigned long getUnsignedLong() const {return d_value.get_ui(); }

  /**
   * Computes the hash of the node from the first word of the
   * numerator, the denominator.
   */
  size_t hash() const {
    return gmpz_hash(d_value.get_mpz_t());
  }

  friend class CVC4::Rational;
};/* class Integer */

std::ostream& operator<<(std::ostream& os, const Integer& n);


}/* CVC4 namespace */

#endif /* __CVC4__RATIONAL_H */

