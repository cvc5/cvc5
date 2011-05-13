/*********************                                                        */
/*! \file cardinality.cpp
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
 ** Implementation of a simple class to represent a cardinality.
 **/

#include "util/cardinality.h"

namespace CVC4 {

const Integer Cardinality::s_unknownCard(0);
const Integer Cardinality::s_intCard(-1);
const Integer Cardinality::s_realCard(-2);

const Cardinality Cardinality::INTEGERS(Cardinality::Beth(0));
const Cardinality Cardinality::REALS(Cardinality::Beth(1));
const Cardinality Cardinality::UNKNOWN((Cardinality::Unknown()));

Cardinality& Cardinality::operator+=(const Cardinality& c) throw() {
  if(isUnknown()) {
    return *this;
  } else if(c.isUnknown()) {
    d_card = s_unknownCard;
    return *this;
  }

  if(isFinite() && c.isFinite()) {
    d_card += c.d_card - 1;
    return *this;
  }
  if(*this >= c) {
    return *this;
  } else {
    return *this = c;
  }
}

/** Assigning multiplication of this cardinality with another. */
Cardinality& Cardinality::operator*=(const Cardinality& c) throw() {
  if(isUnknown()) {
    return *this;
  } else if(c.isUnknown()) {
    d_card = s_unknownCard;
    return *this;
  }

  if(*this == 0 || c == 0) {
    return *this = 0;
  } else if(!isFinite() || !c.isFinite()) {
    if(*this >= c) {
      return *this;
    } else {
      return *this = c;
    }
  } else {
    d_card -= 1;
    d_card *= c.d_card - 1;
    d_card += 1;
    return *this;
  }
}

/** Assigning exponentiation of this cardinality with another. */
Cardinality& Cardinality::operator^=(const Cardinality& c)
  throw(IllegalArgumentException) {
  if(isUnknown()) {
    return *this;
  } else if(c.isUnknown()) {
    d_card = s_unknownCard;
    return *this;
  }

  if(c == 0) {
    // (anything) ^ 0 == 1
    d_card = 2;// remember +1 for finite cardinalities
    return *this;
  } else if(*this == 0) {
    // 0 ^ (>= 1) == 0
    return *this;
  } else if(*this == 1) {
    // 1 ^ (>= 1) == 1
    return *this;
  } else if(c == 1) {
    // (anything) ^ 1 == (that thing)
    return *this;
  } else if(isFinite() && c.isFinite()) {
    // finite ^ finite == finite
    //
    // Note: can throw an assertion if c is too big for
    // exponentiation
    d_card = (d_card - 1).pow(c.d_card.getUnsignedLong() - 1) + 1;
    return *this;
  } else if(!isFinite() && c.isFinite()) {
    // inf ^ finite == inf
    return *this;
  } else {
    Assert(*this >= 2 && !c.isFinite(),
           "fall-through case not as expected:\n%s\n%s",
           this->toString().c_str(), c.toString().c_str());
    // (>= 2) ^ beth_k == beth_(k+1)
    // unless the base is already > the exponent
    if(*this > c) {
      return *this;
    }
    d_card = c.d_card - 1;
    return *this;
  }
}


std::string Cardinality::toString() const throw() {
  std::stringstream ss;
  ss << *this;
  return ss.str();
}


std::ostream& operator<<(std::ostream& out, Cardinality::Beth b) throw() {
  out << "beth[" << b.getNumber() << ']';

  return out;
}


std::ostream& operator<<(std::ostream& out, const Cardinality& c) throw() {
  if(c.isUnknown()) {
    out << "Cardinality::UNKNOWN";
  } else if(c.isFinite()) {
    out << c.getFiniteCardinality();
  } else {
    out << Cardinality::Beth(c.getBethNumber());
  }

  return out;
}


}/* CVC4 namespace */
