/*********************                                                        */
/*! \file integer_cln_imp.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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
#include <iostream>
#include <cln/integer.h>
#include <sstream>
#include <cln/input.h>
#include <cln/integer_io.h>
#include "util/Assert.h"

namespace CVC4 {

class Rational;

class Integer {
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


  Integer operator+(const Integer& y) const{
    return Integer( d_value + y.d_value );
  }

  Integer operator-(const Integer& y) const {
    return Integer( d_value - y.d_value );
  }

  Integer operator*(const Integer& y) const {
    return Integer( d_value * y.d_value );
  }

  /** Raise this Integer to the power <code>exp</code>.
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

  //friend std::ostream& operator<<(std::ostream& os, const Integer& n);

  long getLong() const { return cln::cl_I_to_long(d_value); }
  unsigned long getUnsignedLong() const {return cln::cl_I_to_ulong(d_value); }

  /**
   * Computes the hash of the node from the first word of the
   * numerator, the denominator.
   */
  size_t hash() const {
    return equal_hashcode(d_value);
  }

  friend class CVC4::Rational;
};/* class Integer */

struct IntegerHashStrategy {
  static inline size_t hash(const CVC4::Integer& i) {
    return i.hash();
  }
};/* struct IntegerHashStrategy */

std::ostream& operator<<(std::ostream& os, const Integer& n);

}/* CVC4 namespace */

#endif /* __CVC4__INTEGER_H */

