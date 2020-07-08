/*********************                                                        */
/*! \file cardinality.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of cardinality
 **
 ** Simple class to represent a cardinality; used by the CVC4 type system
 ** give the cardinality of sorts.
 **/

#include "cvc4_public.h"

#ifndef CVC4__CARDINALITY_H
#define CVC4__CARDINALITY_H

#include <iostream>
#include <utility>

#include "base/exception.h"
#include "util/integer.h"

namespace CVC4 {

/**
 * Representation for a Beth number, used only to construct
 * Cardinality objects.
 */
class CVC4_PUBLIC CardinalityBeth {
  Integer d_index;

 public:
  CardinalityBeth(const Integer& beth);

  const Integer& getNumber() const { return d_index; }

}; /* class CardinalityBeth */

/**
 * Representation for an unknown cardinality.
 */
class CVC4_PUBLIC CardinalityUnknown {
 public:
  CardinalityUnknown() {}
  ~CardinalityUnknown() {}
}; /* class CardinalityUnknown */

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

  /** A representation for unknown cardinality */
  static const Integer s_unknownCard;

  /** A representation for large, finite cardinality */
  static const Integer s_largeFiniteCard;

  /**
   * In the case of finite cardinality, this is > 0, and is equal to
   * the cardinality+1.  If infinite, it is < 0, and is Beth[|card|-1].
   * That is, "-1" means Beth 0 == |Z|, "-2" means Beth 1 == |R|, etc.
   * If this field is 0, the cardinality is unknown.
   *
   * We impose a ceiling on finite cardinalities of 2^64.  If this field
   * is >= 2^64 + 1, we consider it at "ceiling" cardinality, and
   * comparisons between all such cardinalities result in "unknown."
   */
  Integer d_card;

 public:
  /** The cardinality of the set of integers. */
  static const Cardinality INTEGERS;

  /** The cardinality of the set of real numbers. */
  static const Cardinality REALS;

  /** The unknown cardinality */
  static const Cardinality UNKNOWN_CARD;

  /** Used as a result code for Cardinality::compare(). */
  enum CVC4_PUBLIC CardinalityComparison {
    LESS,
    EQUAL,
    GREATER,
    UNKNOWN
  }; /* enum CardinalityComparison */

  /**
   * Construct a finite cardinality equal to the integer argument.
   * The argument must be nonnegative.  If we change this to an
   * "unsigned" argument to enforce the restriction, we mask some
   * errors that automatically convert, like "Cardinality(-1)".
   */
  Cardinality(long card);

  /**
   * Construct a finite cardinality equal to the integer argument.
   * The argument must be nonnegative.
   */
  Cardinality(const Integer& card);

  /**
   * Construct an infinite cardinality equal to the given Beth number.
   */
  Cardinality(CardinalityBeth beth) : d_card(-beth.getNumber() - 1) {}

  /**
   * Construct an unknown cardinality.
   */
  Cardinality(CardinalityUnknown) : d_card(0) {}

  /**
   * Returns true iff this cardinality is unknown.  "Unknown" in this
   * sense means that the cardinality is completely unknown; it might
   * be finite, or infinite---anything.  Large, finite cardinalities
   * at the "ceiling" return "false" for isUnknown() and true for
   * isFinite() and isLargeFinite().
   */
  bool isUnknown() const { return d_card == 0; }

  /** Returns true iff this cardinality is finite. */
  bool isFinite() const { return d_card > 0; }
  /** Returns true iff this cardinality is one */
  bool isOne() const { return d_card == 2; }
  /**
   * Returns true iff this cardinality is finite and large (i.e.,
   * at the ceiling of representable finite cardinalities).
   */
  bool isLargeFinite() const { return d_card >= s_largeFiniteCard; }

  /** Returns true iff this cardinality is infinite. */
  bool isInfinite() const { return d_card < 0; }

  /**
   * Returns true iff this cardinality is finite or countably
   * infinite.
   */
  bool isCountable() const { return isFinite() || d_card == s_intCard; }

  /**
   * In the case that this cardinality is finite, return its
   * cardinality.  (If this cardinality is infinite, this function
   * throws an IllegalArgumentException.)
   */
  Integer getFiniteCardinality() const;

  /**
   * In the case that this cardinality is infinite, return its Beth
   * number.  (If this cardinality is finite, this function throws an
   * IllegalArgumentException.)
   */
  Integer getBethNumber() const;

  /** Assigning addition of this cardinality with another. */
  Cardinality& operator+=(const Cardinality& c);

  /** Assigning multiplication of this cardinality with another. */
  Cardinality& operator*=(const Cardinality& c);

  /** Assigning exponentiation of this cardinality with another. */
  Cardinality& operator^=(const Cardinality& c);

  /** Add two cardinalities. */
  Cardinality operator+(const Cardinality& c) const {
    Cardinality card(*this);
    card += c;
    return card;
  }

  /** Multiply two cardinalities. */
  Cardinality operator*(const Cardinality& c) const {
    Cardinality card(*this);
    card *= c;
    return card;
  }

  /**
   * Exponentiation of two cardinalities.
   */
  Cardinality operator^(const Cardinality& c) const {
    Cardinality card(*this);
    card ^= c;
    return card;
  }

  /**
   * Compare two cardinalities.  This can return UNKNOWN if two
   * finite cardinalities are at the ceiling (and thus not precisely
   * represented), or if one or the other is the special "unknown"
   * cardinality.
   */
  Cardinality::CardinalityComparison compare(const Cardinality& c) const;

  /**
   * Return a string representation of this cardinality.
   */
  std::string toString() const;

  /**
   * Compare two cardinalities and if it is known that the current
   * cardinality is smaller or equal to c, it returns true.
   */
  bool knownLessThanOrEqual(const Cardinality& c) const;
}; /* class Cardinality */

/** Print an element of the InfiniteCardinality enumeration. */
std::ostream& operator<<(std::ostream& out, CardinalityBeth b) CVC4_PUBLIC;

/** Print a cardinality in a human-readable fashion. */
std::ostream& operator<<(std::ostream& out, const Cardinality& c) CVC4_PUBLIC;

} /* CVC4 namespace */

#endif /* CVC4__CARDINALITY_H */
