/*********************                                                        */
/*! \file result.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Encapsulation of the result of a query.
 **
 ** Encapsulation of the result of a query.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__RESULT_H
#define __CVC4__RESULT_H

#include <iostream>
#include <string>

#include "base/exception.h"
#include "options/language.h"

namespace CVC4 {

class Result;

std::ostream& operator<<(std::ostream& out, const Result& r) CVC4_PUBLIC;

/**
 * Three-valued SMT result, with optional explanation.
 */
class CVC4_PUBLIC Result {
 public:
  enum Sat { UNSAT = 0, SAT = 1, SAT_UNKNOWN = 2 };

  enum Validity { INVALID = 0, VALID = 1, VALIDITY_UNKNOWN = 2 };

  enum Type { TYPE_SAT, TYPE_VALIDITY, TYPE_NONE };

  enum UnknownExplanation {
    REQUIRES_FULL_CHECK,
    INCOMPLETE,
    TIMEOUT,
    RESOURCEOUT,
    MEMOUT,
    INTERRUPTED,
    NO_STATUS,
    UNSUPPORTED,
    OTHER,
    UNKNOWN_REASON
  };

 private:
  enum Sat d_sat;
  enum Validity d_validity;
  enum Type d_which;
  enum UnknownExplanation d_unknownExplanation;
  std::string d_inputName;

 public:
  Result();

  Result(enum Sat s, std::string inputName = "");

  Result(enum Validity v, std::string inputName = "");

  Result(enum Sat s, enum UnknownExplanation unknownExplanation,
         std::string inputName = "");

  Result(enum Validity v, enum UnknownExplanation unknownExplanation,
         std::string inputName = "");

  Result(const std::string& s, std::string inputName = "");

  Result(const Result& r, std::string inputName) {
    *this = r;
    d_inputName = inputName;
  }

  enum Sat isSat() const { return d_which == TYPE_SAT ? d_sat : SAT_UNKNOWN; }

  enum Validity isValid() const {
    return d_which == TYPE_VALIDITY ? d_validity : VALIDITY_UNKNOWN;
  }

  bool isUnknown() const {
    return isSat() == SAT_UNKNOWN && isValid() == VALIDITY_UNKNOWN;
  }

  Type getType() const { return d_which; }

  bool isNull() const { return d_which == TYPE_NONE; }

  enum UnknownExplanation whyUnknown() const;

  bool operator==(const Result& r) const;
  inline bool operator!=(const Result& r) const;
  Result asSatisfiabilityResult() const;
  Result asValidityResult() const;

  std::string toString() const;

  std::string getInputName() const { return d_inputName; }

  /**
   * Write a Result out to a stream in this language.
   */
  void toStream(std::ostream& out, OutputLanguage language) const;

  /**
   * This is mostly the same the default
   * If getType() == Result::TYPE_SAT && isSat() == Result::SAT_UNKNOWN,
   *
   */
  void toStreamSmt2(std::ostream& out) const;

  /**
   * Write a Result out to a stream in the Tptp format
   */
  void toStreamTptp(std::ostream& out) const;

  /**
   * Write a Result out to a stream.
   *
   * The default implementation writes a reasonable string in lowercase
   * for sat, unsat, valid, invalid, or unknown results.  This behavior
   * is overridable by each Printer, since sometimes an output language
   * has a particular preference for how results should appear.
   */
  void toStreamDefault(std::ostream& out) const;
}; /* class Result */

inline bool Result::operator!=(const Result& r) const { return !(*this == r); }

std::ostream& operator<<(std::ostream& out, enum Result::Sat s) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& out,
                         enum Result::Validity v) CVC4_PUBLIC;
std::ostream& operator<<(std::ostream& out,
                         enum Result::UnknownExplanation e) CVC4_PUBLIC;

bool operator==(enum Result::Sat s, const Result& r) CVC4_PUBLIC;
bool operator==(enum Result::Validity v, const Result& r) CVC4_PUBLIC;

bool operator!=(enum Result::Sat s, const Result& r) CVC4_PUBLIC;
bool operator!=(enum Result::Validity v, const Result& r) CVC4_PUBLIC;

} /* CVC4 namespace */

#endif /* __CVC4__RESULT_H */
