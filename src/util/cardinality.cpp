/*********************                                                        */
/*! \file cardinality.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Representation of cardinality
 **
 ** Implementation of a simple class to represent a cardinality.
 **/

#include "util/cardinality.h"

#include "base/cvc4_assert.h"

namespace CVC4 {

const Integer Cardinality::s_unknownCard(0);
const Integer Cardinality::s_intCard(-1);
const Integer Cardinality::s_realCard(-2);
const Integer Cardinality::s_largeFiniteCard(
    Integer("18446744073709551617"));  // 2^64 + 1

const Cardinality Cardinality::INTEGERS(CardinalityBeth(0));
const Cardinality Cardinality::REALS(CardinalityBeth(1));
const Cardinality Cardinality::UNKNOWN_CARD((CardinalityUnknown()));

CardinalityBeth::CardinalityBeth(const Integer& beth) : d_index(beth) {
  PrettyCheckArgument(beth >= 0, beth,
                      "Beth index must be a nonnegative integer, not %s.",
                      beth.toString().c_str());
}

Cardinality::Cardinality(long card) : d_card(card) {
  PrettyCheckArgument(card >= 0, card,
                      "Cardinality must be a nonnegative integer, not %ld.",
                      card);
  d_card += 1;
}

Cardinality::Cardinality(const Integer& card) : d_card(card) {
  PrettyCheckArgument(card >= 0, card,
                      "Cardinality must be a nonnegative integer, not %s.",
                      card.toString().c_str());
  d_card += 1;
}

Integer Cardinality::getFiniteCardinality() const {
  PrettyCheckArgument(isFinite(), *this, "This cardinality is not finite.");
  PrettyCheckArgument(
      !isLargeFinite(), *this,
      "This cardinality is finite, but too large to represent.");
  return d_card - 1;
}

Integer Cardinality::getBethNumber() const {
  PrettyCheckArgument(!isFinite() && !isUnknown(), *this,
                      "This cardinality is not infinite (or is unknown).");
  return -d_card - 1;
}

Cardinality& Cardinality::operator+=(const Cardinality& c) {
  if (isUnknown()) {
    return *this;
  } else if (c.isUnknown()) {
    d_card = s_unknownCard;
    return *this;
  }

  if (c.isFinite() && isLargeFinite()) {
    return *this;
  } else if (isFinite() && c.isLargeFinite()) {
    d_card = s_largeFiniteCard;
    return *this;
  }

  if (isFinite() && c.isFinite()) {
    d_card += c.d_card - 1;
    return *this;
  }
  if (compare(c) == LESS) {
    return *this = c;
  } else {
    return *this;
  }

  Unreachable();
}

/** Assigning multiplication of this cardinality with another. */
Cardinality& Cardinality::operator*=(const Cardinality& c) {
  if (isUnknown()) {
    return *this;
  } else if (c.isUnknown()) {
    d_card = s_unknownCard;
    return *this;
  }

  if (c.isFinite() && isLargeFinite()) {
    return *this;
  } else if (isFinite() && c.isLargeFinite()) {
    d_card = s_largeFiniteCard;
    return *this;
  }

  if (compare(0) == EQUAL || c.compare(0) == EQUAL) {
    return *this = 0;
  } else if (!isFinite() || !c.isFinite()) {
    if (compare(c) == LESS) {
      return *this = c;
    } else {
      return *this;
    }
  } else {
    d_card -= 1;
    d_card *= c.d_card - 1;
    d_card += 1;
    return *this;
  }

  Unreachable();
}

/** Assigning exponentiation of this cardinality with another. */
Cardinality& Cardinality::operator^=(const Cardinality& c) {
  if (isUnknown()) {
    return *this;
  } else if (c.isUnknown()) {
    d_card = s_unknownCard;
    return *this;
  }

  if (c.isFinite() && isLargeFinite()) {
    return *this;
  } else if (isFinite() && c.isLargeFinite()) {
    d_card = s_largeFiniteCard;
    return *this;
  }

  if (c.compare(0) == EQUAL) {
    // (anything) ^ 0 == 1
    d_card = 2;  // remember, +1 for finite cardinalities
    return *this;
  } else if (compare(0) == EQUAL) {
    // 0 ^ (>= 1) == 0
    return *this;
  } else if (compare(1) == EQUAL) {
    // 1 ^ (>= 1) == 1
    return *this;
  } else if (c.compare(1) == EQUAL) {
    // (anything) ^ 1 == (that thing)
    return *this;
  } else if (isFinite() && c.isFinite()) {
    // finite ^ finite == finite
    try {
      // Note: can throw an assertion if c is too big for
      // exponentiation
      if (d_card - 1 >= 2 && c.d_card - 1 >= 64) {
        // don't bother, it's too large anyways
        d_card = s_largeFiniteCard;
      } else {
        d_card = (d_card - 1).pow(c.d_card.getUnsignedLong() - 1) + 1;
      }
    } catch (IllegalArgumentException&) {
      d_card = s_largeFiniteCard;
    }
    return *this;
  } else if (!isFinite() && c.isFinite()) {
    // inf ^ finite == inf
    return *this;
  } else {
    Assert(compare(2) != LESS && !c.isFinite(),
           "fall-through case not as expected:\n%s\n%s",
           this->toString().c_str(), c.toString().c_str());
    // (>= 2) ^ beth_k == beth_(k+1)
    // unless the base is already > the exponent
    if (compare(c) == GREATER) {
      return *this;
    }
    d_card = c.d_card - 1;
    return *this;
  }

  Unreachable();
}

Cardinality::CardinalityComparison Cardinality::compare(
    const Cardinality& c) const {
  if (isUnknown() || c.isUnknown()) {
    return UNKNOWN;
  } else if (isLargeFinite()) {
    if (c.isLargeFinite()) {
      return UNKNOWN;
    } else if (c.isFinite()) {
      return GREATER;
    } else {
      Assert(c.isInfinite());
      return LESS;
    }
  } else if (c.isLargeFinite()) {
    if (isLargeFinite()) {
      return UNKNOWN;
    } else if (isFinite()) {
      return LESS;
    } else {
      Assert(isInfinite());
      return GREATER;
    }
  } else if (isInfinite()) {
    if (c.isFinite()) {
      return GREATER;
    } else {
      return d_card < c.d_card ? GREATER : (d_card == c.d_card ? EQUAL : LESS);
    }
  } else if (c.isInfinite()) {
    Assert(isFinite());
    return LESS;
  } else {
    Assert(isFinite() && !isLargeFinite());
    Assert(c.isFinite() && !c.isLargeFinite());
    return d_card < c.d_card ? LESS : (d_card == c.d_card ? EQUAL : GREATER);
  }

  Unreachable();
}

bool Cardinality::knownLessThanOrEqual(const Cardinality& c) const {
  CardinalityComparison cmp = this->compare(c);
  return cmp == LESS || cmp == EQUAL;
}

std::string Cardinality::toString() const {
  std::stringstream ss;
  ss << *this;
  return ss.str();
}

std::ostream& operator<<(std::ostream& out, CardinalityBeth b) {
  out << "beth[" << b.getNumber() << ']';

  return out;
}

std::ostream& operator<<(std::ostream& out, const Cardinality& c) {
  if (c.isUnknown()) {
    out << "Cardinality::UNKNOWN";
  } else if (c.isFinite()) {
    out << c.getFiniteCardinality();
  } else {
    out << CardinalityBeth(c.getBethNumber());
  }

  return out;
}

} /* CVC4 namespace */
