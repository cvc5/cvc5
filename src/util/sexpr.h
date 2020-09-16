/*********************                                                        */
/*! \file sexpr.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters, Christopher L. Conway
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simple representation of S-expressions
 **
 ** Simple representation of S-expressions.
 ** These are used when a simple, and obvious interface for basic
 ** expressions is appropriate.
 **
 ** These are quite ineffecient.
 ** These are totally disconnected from any ExprManager.
 ** These keep unique copies of all of their children.
 ** These are VERY overly verbose and keep much more data than is needed.
 **/

#include "cvc4_public.h"

#ifndef CVC4__SEXPR_H
#define CVC4__SEXPR_H

#include <iomanip>
#include <iosfwd>
#include <string>
#include <vector>

#include "base/exception.h"
#include "options/language.h"
#include "util/integer.h"
#include "util/rational.h"

namespace CVC4 {

class CVC4_PUBLIC SExprKeyword {
 public:
  SExprKeyword(const std::string& s) : d_str(s) {}
  const std::string& getString() const { return d_str; }

 private:
  std::string d_str;
}; /* class SExpr::Keyword */

/**
 * A simple S-expression. An S-expression is either an atom with a
 * string value, or a list of other S-expressions.
 */
class CVC4_PUBLIC SExpr {
 public:
  typedef SExprKeyword Keyword;

  SExpr();
  SExpr(const SExpr&);
  SExpr& operator=(const SExpr& other);
  ~SExpr();

  SExpr(const CVC4::Integer& value);

  SExpr(int value);
  SExpr(long int value);
  SExpr(unsigned int value);
  SExpr(unsigned long int value);

  SExpr(const CVC4::Rational& value);

  SExpr(const std::string& value);

  /**
   * This constructs a string expression from a const char* value.
   * This cannot be removed in order to support SExpr("foo").
   * Given the other constructors this SExpr("foo") converts to bool.
   * instead of SExpr(string("foo")).
   */
  SExpr(const char* value);

  /**
   * This adds a convenience wrapper to SExpr to cast from bools.
   * This is internally handled as the strings "true" and "false"
   */
  SExpr(bool value);
  SExpr(const Keyword& value);
  SExpr(const std::vector<SExpr>& children);

  /** Is this S-expression an atom? */
  bool isAtom() const;

  /** Is this S-expression an integer? */
  bool isInteger() const;

  /** Is this S-expression a rational? */
  bool isRational() const;

  /** Is this S-expression a string? */
  bool isString() const;

  /** Is this S-expression a keyword? */
  bool isKeyword() const;

  /**
   * This wraps the toStream() printer.
   * NOTE: toString() and getValue() may differ on Keywords based on
   * the current language set in expr.
   */
  std::string toString() const;

  /**
   * Get the string value of this S-expression. This will cause an
   * error if this S-expression is not an atom.
   */
  std::string getValue() const;

  /**
   * Get the integer value of this S-expression. This will cause an
   * error if this S-expression is not an integer.
   */
  const CVC4::Integer& getIntegerValue() const;

  /**
   * Get the rational value of this S-expression. This will cause an
   * error if this S-expression is not a rational.
   */
  const CVC4::Rational& getRationalValue() const;

  /**
   * Get the children of this S-expression. This will cause an error
   * if this S-expression is not a list.
   */
  const std::vector<SExpr>& getChildren() const;

  /** Is this S-expression equal to another? */
  bool operator==(const SExpr& s) const;

  /** Is this S-expression different from another? */
  bool operator!=(const SExpr& s) const;

  /**
   * This returns the best match in the following order:
   * match atom with
   *  "true", "false" -> SExpr(value)
   * | is and integer -> as integer
   * | is a rational -> as rational
   * | _ -> SExpr()
   */
  static SExpr parseAtom(const std::string& atom);

  /**
   * Parses a list of atoms.
   */
  static SExpr parseListOfAtoms(const std::vector<std::string>& atoms);

  /**
   * Parses a list of list of atoms.
   */
  static SExpr parseListOfListOfAtoms(
      const std::vector<std::vector<std::string> >& atoms_lists);

  /**
   * Outputs the SExpr onto the ostream out. This version reads defaults to the
   * OutputLanguage, language::SetLanguage::getLanguage(out). The indent level
   * is
   * set to 2 if PrettySExprs::getPrettySExprs() is on and is 0 otherwise.
   */
  static void toStream(std::ostream& out, const SExpr& sexpr);

  /**
   * Outputs the SExpr onto the ostream out. This version sets the indent level
   * to 2 if PrettySExprs::getPrettySExprs() is on.
   */
  static void toStream(std::ostream& out, const SExpr& sexpr,
                       OutputLanguage language);

  /**
   * Outputs the SExpr onto the ostream out.
   * If the languageQuotesKeywords(language), then a top level keyword, " X",
   * that needs quoting according to the SMT2 language standard is printed with
   * quotes, "| X|".
   * Otherwise this prints using toStreamRec().
   *
   * TIM: Keywords that are children are not currently quoted. This seems
   * incorrect but I am just reproduicing the old behavior even if it does not
   * make
   * sense.
   */
  static void toStream(std::ostream& out, const SExpr& sexpr,
                       OutputLanguage language, int indent);

 private:
  /**
   * Simple printer for SExpr to an ostream.
   * The current implementation is language independent.
   */
  static void toStreamRec(std::ostream& out, const SExpr& sexpr,
                          OutputLanguage language, int indent);

  /** Returns true if this language quotes Keywords when printing. */
  static bool languageQuotesKeywords(OutputLanguage language);

  enum SExprTypes {
    SEXPR_STRING,
    SEXPR_KEYWORD,
    SEXPR_INTEGER,
    SEXPR_RATIONAL,
    SEXPR_NOT_ATOM
  } d_sexprType;

  /** The value of an atomic integer-valued S-expression. */
  CVC4::Integer d_integerValue;

  /** The value of an atomic rational-valued S-expression. */
  CVC4::Rational d_rationalValue;

  /** The value of an atomic S-expression. */
  std::string d_stringValue;

  typedef std::vector<SExpr> SExprVector;

  /**
   * The children of a list S-expression.
   * Whenever the SExpr isAtom() holds, this points at NULL.
   *
   * This should be a pointer in case the implementation of vector<SExpr> ever
   * directly contained or allocated an SExpr. If this happened this would
   * trigger,
   * either the size being infinite or SExpr() being an infinite loop.
   */
  SExprVector* d_children;
}; /* class SExpr */

/** Prints an SExpr. */
std::ostream& operator<<(std::ostream& out, const SExpr& sexpr) CVC4_PUBLIC;

/**
 * IOStream manipulator to pretty-print SExprs.
 */
class CVC4_PUBLIC PrettySExprs {
  /**
   * The allocated index in ios_base for our setting.
   */
  static const int s_iosIndex;

  /**
   * When this manipulator is used, the setting is stored here.
   */
  bool d_prettySExprs;

 public:
  /**
   * Construct a PrettySExprs with the given setting.
   */
  PrettySExprs(bool prettySExprs) : d_prettySExprs(prettySExprs) {}

  inline void applyPrettySExprs(std::ostream& out) {
    out.iword(s_iosIndex) = d_prettySExprs;
  }

  static inline bool getPrettySExprs(std::ostream& out) {
    return out.iword(s_iosIndex);
  }

  static inline void setPrettySExprs(std::ostream& out, bool prettySExprs) {
    out.iword(s_iosIndex) = prettySExprs;
  }

  /**
   * Set the pretty-sexprs state on the output stream for the current
   * stack scope.  This makes sure the old state is reset on the
   * stream after normal OR exceptional exit from the scope, using the
   * RAII C++ idiom.
   */
  class Scope {
    std::ostream& d_out;
    bool d_oldPrettySExprs;

   public:
    inline Scope(std::ostream& out, bool prettySExprs)
        : d_out(out), d_oldPrettySExprs(PrettySExprs::getPrettySExprs(out)) {
      PrettySExprs::setPrettySExprs(out, prettySExprs);
    }

    inline ~Scope() { PrettySExprs::setPrettySExprs(d_out, d_oldPrettySExprs); }

  }; /* class PrettySExprs::Scope */

}; /* class PrettySExprs */

/**
 * Sets the default pretty-sexprs setting for an ostream.  Use like this:
 *
 *   // let out be an ostream, s an SExpr
 *   out << PrettySExprs(true) << s << endl;
 *
 * The setting stays permanently (until set again) with the stream.
 */
std::ostream& operator<<(std::ostream& out, PrettySExprs ps);

} /* CVC4 namespace */

#endif /* CVC4__SEXPR_H */
