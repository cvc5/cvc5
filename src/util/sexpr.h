/*********************                                                        */
/*! \file sexpr.h
 ** \verbatim
 ** Original author: cconway
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Simple representation of SMT S-expressions.
 **
 ** Simple representation of SMT S-expressions.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__SEXPR_H
#define __CVC4__SEXPR_H

#include <vector>
#include <string>

#include "util/Assert.h"

namespace CVC4 {

/**
 * A simple S-expression. An S-expression is either an atom with a
 * string value, or a list of other S-expressions.
 */
class CVC4_PUBLIC SExpr {

  enum {
    SEXPR_STRING,
    SEXPR_INTEGER,
    SEXPR_RATIONAL,
    SEXPR_NOT_ATOM
  } d_atomType;

  /** The value of an atomic integer-valued S-expression. */
  Integer d_integerValue;

  /** The value of an atomic rational-valued S-expression. */
  Rational d_rationalValue;

  /** The value of an atomic S-expression. */
  std::string d_stringValue;

  /** The children of a list S-expression. */
  std::vector<SExpr> d_children;

public:
  SExpr() :
    d_atomType(SEXPR_STRING),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  SExpr(const Integer& value) :
    d_atomType(SEXPR_INTEGER),
    d_integerValue(value),
    d_rationalValue(0),
    d_stringValue(""),
    d_children() {
  }

  SExpr(const Rational& value) :
    d_atomType(SEXPR_RATIONAL),
    d_integerValue(0),
    d_rationalValue(value),
    d_stringValue(""),
    d_children() {
  }

  SExpr(const std::string& value) :
    d_atomType(SEXPR_STRING),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(value),
    d_children() {
  }

  SExpr(const std::vector<SExpr> children) :
    d_atomType(SEXPR_NOT_ATOM),
    d_integerValue(0),
    d_rationalValue(0),
    d_stringValue(""),
    d_children(children) {
  }

  /** Is this S-expression an atom? */
  bool isAtom() const;

  /** Is this S-expression an integer? */
  bool isInteger() const;

  /** Is this S-expression a rational? */
  bool isRational() const;

  /** Is this S-expression a string? */
  bool isString() const;

  /**
   * Get the string value of this S-expression. This will cause an
   * error if this S-expression is not an atom.
   */
  const std::string getValue() const;

  /**
   * Get the integer value of this S-expression. This will cause an
   * error if this S-expression is not an integer.
   */
  const Integer& getIntegerValue() const;

  /**
   * Get the rational value of this S-expression. This will cause an
   * error if this S-expression is not a rational.
   */
  const Rational& getRationalValue() const;

  /**
   * Get the children of this S-expression. This will cause an error
   * if this S-expression is not a list.
   */
  const std::vector<SExpr> getChildren() const;

};/* class SExpr */

inline bool SExpr::isAtom() const {
  return d_atomType != SEXPR_NOT_ATOM;
}

inline bool SExpr::isInteger() const {
  return d_atomType == SEXPR_INTEGER;
}

inline bool SExpr::isRational() const {
  return d_atomType == SEXPR_RATIONAL;
}

inline bool SExpr::isString() const {
  return d_atomType == SEXPR_STRING;
}

inline const std::string SExpr::getValue() const {
  AlwaysAssert( isAtom() );
  switch(d_atomType) {
  case SEXPR_INTEGER:
    return d_integerValue.toString();
  case SEXPR_RATIONAL:
    return d_rationalValue.toString();
  case SEXPR_STRING:
    return d_stringValue;
  default:
    Unhandled(d_atomType);
  }
  return d_stringValue;
}

inline const Integer& SExpr::getIntegerValue() const {
  AlwaysAssert( isInteger() );
  return d_integerValue;
}

inline const Rational& SExpr::getRationalValue() const {
  AlwaysAssert( isRational() );
  return d_rationalValue;
}

inline const std::vector<SExpr> SExpr::getChildren() const {
  AlwaysAssert( !isAtom() );
  return d_children;
}

inline std::ostream& operator<<(std::ostream& out, const SExpr& sexpr) {
  if( sexpr.isAtom() ) {
    out << sexpr.getValue();
  } else {
    std::vector<SExpr> children = sexpr.getChildren();
    out << "(";
    bool first = true;
    for( std::vector<SExpr>::iterator it = children.begin();
         it != children.end();
         ++it ) {
      if( first ) {
        first = false;
      } else {
        out << " ";
      }
        out << *it;
    }
    out << ")";
  }
  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__SEXPR_H */
