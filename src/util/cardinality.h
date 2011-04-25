/*********************                                                        */
/*! \file cardinality.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Representation of cardinality
 **
 ** Simple class to represent a cardinality; used by the CVC4 type system
 ** give the cardinality of sorts.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__CARDINALITY_H
#define __CVC4__CARDINALITY_H

#include <iostream>
#include <utility>

#include "util/integer.h"
#include "util/Assert.h"

namespace CVC4 {

/**
 * A simple representation of a cardinality.  We store an
 * arbitrary-precision integer for finite cardinalities, and we
 * distinguish infinite cardinalities represented as Beth numbers.
 */
class CVC4_PUBLIC Cardinality {
  /** Cardinality of the integers */
  static const Integer s_intCard;

  /** Cardinality of the reals */
  static const Integer s_realCard;

  /**
   * In the case of finite cardinality, this is >= 0, and is equal to
   * the cardinality.  If infinite, it is < 0, and is Beth[|card|-1].
   * That is, "-1" means Beth 0 == |Z|, "-2" means Beth 1 == |R|, etc.
   */
  Integer d_card;

public:

  /** The cardinality of the set of integers. */
  static const Cardinality INTEGERS;

  /** The cardinality of the set of real numbers. */
  static const Cardinality REALS;

  /**
   * Representation for a Beth number, used only to construct
   * Cardinality objects.
   */
  class Beth {
    Integer d_index;

  public:
    Beth(const Integer& beth) : d_index(beth) {
      CheckArgument(beth >= 0, beth,
                    "Beth index must be a nonnegative integer, not %s.",
                    beth.toString().c_str());
    }

    const Integer& getNumber() const throw() {
      return d_index;
    }
  };/* class Cardinality::Beth */

  /**
   * Construct a finite cardinality equal to the integer argument.
   * The argument must be nonnegative.  If we change this to an
   * "unsigned" argument to enforce the restriction, we mask some
   * errors that automatically convert, like "Cardinality(-1)".
   */
  Cardinality(long card) : d_card(card) {
    CheckArgument(card >= 0, card,
                  "Cardinality must be a nonnegative integer, not %ld.", card);
    Assert(isFinite());
  }

  /**
   * Construct a finite cardinality equal to the integer argument.
   * The argument must be nonnegative.
   */
  Cardinality(const Integer& card) : d_card(card) {
    CheckArgument(card >= 0, card,
                  "Cardinality must be a nonnegative integer, not %s.",
                  card.toString().c_str());
    Assert(isFinite());
  }

  /**
   * Construct an infinite cardinality equal to the given Beth number.
   */
  Cardinality(Beth beth) : d_card(-beth.getNumber() - 1) {
    Assert(!isFinite());
  }

  /** Returns true iff this cardinality is finite. */
  bool isFinite() const throw() {
    return d_card >= 0;
  }

  /**
   * Returns true iff this cardinality is finite or countably
   * infinite.
   */
  bool isCountable() const throw() {
    return d_card >= s_intCard;
  }

  /**
   * In the case that this cardinality is finite, return its
   * cardinality.  (If this cardinality is infinite, this function
   * throws an IllegalArgumentException.)
   */
  const Integer& getFiniteCardinality() const throw(IllegalArgumentException) {
    CheckArgument(isFinite(), *this, "This cardinality is not finite.");
    return d_card;
  }

  /**
   * In the case that this cardinality is infinite, return its Beth
   * number.  (If this cardinality is finite, this function throws an
   * IllegalArgumentException.)
   */
  Integer getBethNumber() const throw(IllegalArgumentException) {
    CheckArgument(!isFinite(), *this, "This cardinality is not infinite.");
    return -d_card - 1;
  }

  /** Assigning addition of this cardinality with another. */
  Cardinality& operator+=(const Cardinality& c) throw();

  /** Assigning multiplication of this cardinality with another. */
  Cardinality& operator*=(const Cardinality& c) throw();

  /** Assigning exponentiation of this cardinality with another. */
  Cardinality& operator^=(const Cardinality& c) throw(IllegalArgumentException);

  /** Add two cardinalities. */
  Cardinality operator+(const Cardinality& c) const throw() {
    Cardinality card(*this);
    card += c;
    return card;
  }

  /** Multiply two cardinalities. */
  Cardinality operator*(const Cardinality& c) const throw() {
    Cardinality card(*this);
    card *= c;
    return card;
  }

  /**
   * Exponentiation of two cardinalities.  Throws an exception if both
   * are finite and the exponent is too large.
   */
  Cardinality operator^(const Cardinality& c) const throw(IllegalArgumentException) {
    Cardinality card(*this);
    card ^= c;
    return card;
  }

  /** Test for equality between cardinalities. */
  bool operator==(const Cardinality& c) const throw() {
    return d_card == c.d_card;
  }

  /** Test for disequality between cardinalities. */
  bool operator!=(const Cardinality& c) const throw() {
    return !(*this == c);
  }

  /** Test whether this cardinality is less than another. */
  bool operator<(const Cardinality& c) const throw() {
    return
      ( isFinite() && !c.isFinite() ) ||
      ( isFinite() && c.isFinite() && d_card < c.d_card ) ||
      ( !isFinite() && !c.isFinite() && d_card > c.d_card );
  }

  /**
   * Test whether this cardinality is less than or equal to
   * another.
   */
  bool operator<=(const Cardinality& c) const throw() {
    return *this < c || *this == c;
  }

  /** Test whether this cardinality is greater than another. */
  bool operator>(const Cardinality& c) const throw() {
    return !(*this <= c);
  }

  /**
   * Test whether this cardinality is greater than or equal to
   * another.
   */
  bool operator>=(const Cardinality& c) const throw() {
    return !(*this < c);
  }

  /**
   * Return a string representation of this cardinality.
   */
  std::string toString() const throw();

};/* class Cardinality */


/** Print an element of the InfiniteCardinality enumeration. */
std::ostream& operator<<(std::ostream& out, Cardinality::Beth b)
  throw() CVC4_PUBLIC;


/** Print a cardinality in a human-readable fashion. */
std::ostream& operator<<(std::ostream& out, const Cardinality& c)
  throw() CVC4_PUBLIC;


}/* CVC4 namespace */

#endif /* __CVC4__CARDINALITY_H */
