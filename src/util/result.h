/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Encapsulation of the result of a query.
 */

#include "cvc5_public.h"

#ifndef CVC5__RESULT_H
#define CVC5__RESULT_H

#include <iosfwd>
#include <string>

#include "options/language.h"

namespace cvc5 {

class Result;

std::ostream& operator<<(std::ostream& out, const Result& r);

/**
 * Three-valued SMT result, with optional explanation.
 */
class Result
{
 public:
  enum Status {
    NULL,
    UNSAT, 
    SAT, 
    UNKNOWN
  };

  enum UnknownExplanation
  {
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

 public:
  Result();

  Result(Status s, std::string inputName = "");

  Result(Status s, enum UnknownExplanation unknownExplanation,
         std::string inputName = "");

  Result(const std::string& s, std::string inputName = "");

  Result(const Result& r, std::string inputName) {
    *this = r;
    d_inputName = inputName;
  }

  Status getStatus() const { return d_status; }

  bool isUnknown() const {
    return d_status==UNKNOWN;
  }

  UnknownExplanation getUnknownExplanation() const;

  std::string toString() const;

  std::string getInputName() const { return d_inputName; }

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
   * for sat, unsat, entailed, not entailed, or unknown results.  This behavior
   * is overridable by each Printer, since sometimes an output language
   * has a particular preference for how results should appear.
   */
  void toStreamDefault(std::ostream& out) const;

 private:
  /** The result */
  Status d_status;
  /** The unknown explanation */
  UnknownExplanation d_unknownExplanation;
  /** The input name */
  std::string d_inputName;
}; /* class Result */

inline bool Result::operator!=(const Result& r) const { return !(*this == r); }

std::ostream& operator<<(std::ostream& out, enum Result::Status s);
std::ostream& operator<<(std::ostream& out, enum Result::UnknownExplanation e);

}  // namespace cvc5

#endif /* CVC5__RESULT_H */
