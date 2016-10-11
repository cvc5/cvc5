/*********************                                                        */
/*! \file sexpr.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simple representation of S-expressions
 **
 ** Simple representation of S-expressions.
 **
 ** SExprs have their own language specific printing procedures. The reason for
 ** this being implemented on SExpr and not on the Printer class is that the
 ** Printer class lives in libcvc4. It has to currently as it prints fairly
 ** complicated objects, like Model, which in turn uses SmtEngine pointers.
 ** However, SExprs need to be printed by Statistics. To get the output
 ** consistent with the previous version, the printing of SExprs in different
 ** languages is handled in the SExpr class and the libexpr library.
 **/

#include "util/sexpr.h"

#include <iostream>
#include <sstream>
#include <vector>

#include "base/cvc4_assert.h"
#include "options/set_language.h"
#include "util/smt2_quote_string.h"

namespace CVC4 {

const int PrettySExprs::s_iosIndex = std::ios_base::xalloc();

std::ostream& operator<<(std::ostream& out, PrettySExprs ps) {
  ps.applyPrettySExprs(out);
  return out;
}

SExpr::~SExpr() {
  if (d_children != NULL) {
    delete d_children;
    d_children = NULL;
  }
  Assert(d_children == NULL);
}

SExpr& SExpr::operator=(const SExpr& other) {
  d_sexprType = other.d_sexprType;
  d_integerValue = other.d_integerValue;
  d_rationalValue = other.d_rationalValue;
  d_stringValue = other.d_stringValue;

  if (d_children == NULL && other.d_children == NULL) {
    // Do nothing.
  } else if (d_children == NULL) {
    d_children = new SExprVector(*other.d_children);
  } else if (other.d_children == NULL) {
    delete d_children;
    d_children = NULL;
  } else {
    (*d_children) = other.getChildren();
  }
  Assert(isAtom() == other.isAtom());
  Assert((d_children == NULL) == isAtom());
  return *this;
}

SExpr::SExpr()
    : d_sexprType(SEXPR_STRING),
      d_integerValue(0),
      d_rationalValue(0),
      d_stringValue(""),
      d_children(NULL) {}

SExpr::SExpr(const SExpr& other)
    : d_sexprType(other.d_sexprType),
      d_integerValue(other.d_integerValue),
      d_rationalValue(other.d_rationalValue),
      d_stringValue(other.d_stringValue),
      d_children(NULL) {
  d_children =
      (other.d_children == NULL) ? NULL : new SExprVector(*other.d_children);
  // d_children being NULL is equivalent to the node being an atom.
  Assert((d_children == NULL) == isAtom());
}

SExpr::SExpr(const CVC4::Integer& value)
    : d_sexprType(SEXPR_INTEGER),
      d_integerValue(value),
      d_rationalValue(0),
      d_stringValue(""),
      d_children(NULL) {}

SExpr::SExpr(int value)
    : d_sexprType(SEXPR_INTEGER),
      d_integerValue(value),
      d_rationalValue(0),
      d_stringValue(""),
      d_children(NULL) {}

SExpr::SExpr(long int value)
    : d_sexprType(SEXPR_INTEGER),
      d_integerValue(value),
      d_rationalValue(0),
      d_stringValue(""),
      d_children(NULL) {}

SExpr::SExpr(unsigned int value)
    : d_sexprType(SEXPR_INTEGER),
      d_integerValue(value),
      d_rationalValue(0),
      d_stringValue(""),
      d_children(NULL) {}

SExpr::SExpr(unsigned long int value)
    : d_sexprType(SEXPR_INTEGER),
      d_integerValue(value),
      d_rationalValue(0),
      d_stringValue(""),
      d_children(NULL) {}

SExpr::SExpr(const CVC4::Rational& value)
    : d_sexprType(SEXPR_RATIONAL),
      d_integerValue(0),
      d_rationalValue(value),
      d_stringValue(""),
      d_children(NULL) {}

SExpr::SExpr(const std::string& value)
    : d_sexprType(SEXPR_STRING),
      d_integerValue(0),
      d_rationalValue(0),
      d_stringValue(value),
      d_children(NULL) {}

/**
 * This constructs a string expression from a const char* value.
 * This cannot be removed in order to support SExpr("foo").
 * Given the other constructors this SExpr("foo") converts to bool.
 * instead of SExpr(string("foo")).
 */
SExpr::SExpr(const char* value)
    : d_sexprType(SEXPR_STRING),
      d_integerValue(0),
      d_rationalValue(0),
      d_stringValue(value),
      d_children(NULL) {}

SExpr::SExpr(bool value)
    : d_sexprType(SEXPR_KEYWORD),
      d_integerValue(0),
      d_rationalValue(0),
      d_stringValue(value ? "true" : "false"),
      d_children(NULL) {}

SExpr::SExpr(const Keyword& value)
    : d_sexprType(SEXPR_KEYWORD),
      d_integerValue(0),
      d_rationalValue(0),
      d_stringValue(value.getString()),
      d_children(NULL) {}

SExpr::SExpr(const std::vector<SExpr>& children)
    : d_sexprType(SEXPR_NOT_ATOM),
      d_integerValue(0),
      d_rationalValue(0),
      d_stringValue(""),
      d_children(new SExprVector(children)) {}

std::string SExpr::toString() const {
  std::stringstream ss;
  ss << (*this);
  return ss.str();
}

/** Is this S-expression an atom? */
bool SExpr::isAtom() const { return d_sexprType != SEXPR_NOT_ATOM; }

/** Is this S-expression an integer? */
bool SExpr::isInteger() const { return d_sexprType == SEXPR_INTEGER; }

/** Is this S-expression a rational? */
bool SExpr::isRational() const { return d_sexprType == SEXPR_RATIONAL; }

/** Is this S-expression a string? */
bool SExpr::isString() const { return d_sexprType == SEXPR_STRING; }

/** Is this S-expression a keyword? */
bool SExpr::isKeyword() const { return d_sexprType == SEXPR_KEYWORD; }

std::ostream& operator<<(std::ostream& out, const SExpr& sexpr) {
  SExpr::toStream(out, sexpr);
  return out;
}

void SExpr::toStream(std::ostream& out, const SExpr& sexpr) {
  toStream(out, sexpr, language::SetLanguage::getLanguage(out));
}

void SExpr::toStream(std::ostream& out, const SExpr& sexpr,
                     OutputLanguage language) {
  const int indent = PrettySExprs::getPrettySExprs(out) ? 2 : 0;
  toStream(out, sexpr, language, indent);
}

void SExpr::toStream(std::ostream& out, const SExpr& sexpr,
                     OutputLanguage language, int indent) {
  if (sexpr.isKeyword() && languageQuotesKeywords(language)) {
    out << quoteSymbol(sexpr.getValue());
  } else {
    toStreamRec(out, sexpr, language, indent);
  }
}

void SExpr::toStreamRec(std::ostream& out, const SExpr& sexpr,
                        OutputLanguage language, int indent) {
  if (sexpr.isInteger()) {
    out << sexpr.getIntegerValue();
  } else if (sexpr.isRational()) {
    const double approximation = sexpr.getRationalValue().getDouble();
    out << std::fixed << approximation;
  } else if (sexpr.isKeyword()) {
    out << sexpr.getValue();
  } else if (sexpr.isString()) {
    std::string s = sexpr.getValue();
    // escape backslash and quote
    for (size_t i = 0; i < s.length(); ++i) {
      if (s[i] == '"') {
        s.replace(i, 1, "\\\"");
        ++i;
      } else if (s[i] == '\\') {
        s.replace(i, 1, "\\\\");
        ++i;
      }
    }
    out << "\"" << s << "\"";
  } else {
    const std::vector<SExpr>& kids = sexpr.getChildren();
    out << (indent > 0 && kids.size() > 1 ? "( " : "(");
    bool first = true;
    for (std::vector<SExpr>::const_iterator i = kids.begin(); i != kids.end();
         ++i) {
      if (first) {
        first = false;
      } else {
        if (indent > 0) {
          out << "\n" << std::string(indent, ' ');
        } else {
          out << ' ';
        }
      }
      toStreamRec(out, *i, language,
                  indent <= 0 || indent > 2 ? 0 : indent + 2);
    }
    if (indent > 0 && kids.size() > 1) {
      out << '\n';
      if (indent > 2) {
        out << std::string(indent - 2, ' ');
      }
    }
    out << ')';
  }
} /* toStreamRec() */

bool SExpr::languageQuotesKeywords(OutputLanguage language) {
  switch (language) {
    case language::output::LANG_SMTLIB_V1:
    case language::output::LANG_SMTLIB_V2_0:
    case language::output::LANG_SMTLIB_V2_5:
    case language::output::LANG_SYGUS:
    case language::output::LANG_TPTP:
    case language::output::LANG_Z3STR:
      return true;
    case language::output::LANG_AST:
    case language::output::LANG_CVC3:
    case language::output::LANG_CVC4:
    default:
      return false;
  };
}

std::string SExpr::getValue() const {
  PrettyCheckArgument(isAtom(), this);
  switch (d_sexprType) {
    case SEXPR_INTEGER:
      return d_integerValue.toString();
    case SEXPR_RATIONAL: {
      // We choose to represent rationals as decimal strings rather than
      // "numerator/denominator."  Perhaps an additional SEXPR_DECIMAL
      // could be added if we need both styles, even if it's backed by
      // the same Rational object.
      std::stringstream ss;
      ss << std::fixed << d_rationalValue.getDouble();
      return ss.str();
    }
    case SEXPR_STRING:
    case SEXPR_KEYWORD:
      return d_stringValue;
    case SEXPR_NOT_ATOM:
      return std::string();
  }
  return std::string();
}

const CVC4::Integer& SExpr::getIntegerValue() const {
  PrettyCheckArgument(isInteger(), this);
  return d_integerValue;
}

const CVC4::Rational& SExpr::getRationalValue() const {
  PrettyCheckArgument(isRational(), this);
  return d_rationalValue;
}

const std::vector<SExpr>& SExpr::getChildren() const {
  PrettyCheckArgument(!isAtom(), this);
  Assert(d_children != NULL);
  return *d_children;
}

bool SExpr::operator==(const SExpr& s) const {
  if (d_sexprType == s.d_sexprType && d_integerValue == s.d_integerValue &&
      d_rationalValue == s.d_rationalValue &&
      d_stringValue == s.d_stringValue) {
    if (d_children == NULL && s.d_children == NULL) {
      return true;
    } else if (d_children != NULL && s.d_children != NULL) {
      return getChildren() == s.getChildren();
    }
  }
  return false;
}

bool SExpr::operator!=(const SExpr& s) const { return !(*this == s); }

SExpr SExpr::parseAtom(const std::string& atom) {
  if (atom == "true") {
    return SExpr(true);
  } else if (atom == "false") {
    return SExpr(false);
  } else {
    try {
      Integer z(atom);
      return SExpr(z);
    } catch (std::invalid_argument&) {
      // Fall through to the next case
    }
    try {
      Rational q(atom);
      return SExpr(q);
    } catch (std::invalid_argument&) {
      // Fall through to the next case
    }
    return SExpr(atom);
  }
}

SExpr SExpr::parseListOfAtoms(const std::vector<std::string>& atoms) {
  std::vector<SExpr> parsedAtoms;
  typedef std::vector<std::string>::const_iterator const_iterator;
  for (const_iterator i = atoms.begin(), i_end = atoms.end(); i != i_end; ++i) {
    parsedAtoms.push_back(parseAtom(*i));
  }
  return SExpr(parsedAtoms);
}

SExpr SExpr::parseListOfListOfAtoms(
    const std::vector<std::vector<std::string> >& atoms_lists) {
  std::vector<SExpr> parsedListsOfAtoms;
  typedef std::vector<std::vector<std::string> >::const_iterator const_iterator;
  for (const_iterator i = atoms_lists.begin(), i_end = atoms_lists.end();
       i != i_end; ++i) {
    parsedListsOfAtoms.push_back(parseListOfAtoms(*i));
  }
  return SExpr(parsedListsOfAtoms);
}

} /* CVC4 namespace */
