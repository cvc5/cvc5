/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Encapsulation of the result of a query.
 */
#include "util/result.h"

#include <algorithm>
#include <cctype>
#include <iostream>
#include <sstream>
#include <string>

#include "base/check.h"
#include "options/io_utils.h"

using namespace std;

namespace cvc5::internal {

Result::Result()
    : d_status(NONE), d_unknownExplanation(UNKNOWN_REASON), d_inputName("")
{
}

Result::Result(Status s, std::string inputName)
    : d_status(s), d_unknownExplanation(UNKNOWN_REASON), d_inputName(inputName)
{
  Assert(s != UNKNOWN)
      << "Must provide a reason for satisfiability being unknown";
}

Result::Result(Status s,
               UnknownExplanation unknownExplanation,
               std::string inputName)
    : d_status(s),
      d_unknownExplanation(unknownExplanation),
      d_inputName(inputName)
{
  Assert(s == UNKNOWN) << "improper use of unknown-result constructor";
}

Result::Result(const std::string& instr, std::string inputName)
    : d_status(NONE),
      d_unknownExplanation(UNKNOWN_REASON),
      d_inputName(inputName)
{
  std::string s = instr;
  transform(s.begin(), s.end(), s.begin(), ::tolower);
  if (s == "sat" || s == "satisfiable")
  {
    d_status = SAT;
  }
  else if (s == "unsat" || s == "unsatisfiable")
  {
    d_status = UNSAT;
  }
  else if (s == "incomplete")
  {
    d_status = UNKNOWN;
    d_unknownExplanation = INCOMPLETE;
  }
  else if (s == "timeout")
  {
    d_status = UNKNOWN;
    d_unknownExplanation = TIMEOUT;
  }
  else if (s == "resourceout")
  {
    d_status = UNKNOWN;
    d_unknownExplanation = RESOURCEOUT;
  }
  else if (s == "memout")
  {
    d_status = UNKNOWN;
    d_unknownExplanation = MEMOUT;
  }
  else if (s == "interrupted")
  {
    d_status = UNKNOWN;
    d_unknownExplanation = INTERRUPTED;
  }
  else if (s.size() >= 7 && s.compare(0, 7, "unknown") == 0)
  {
    d_status = UNKNOWN;
  }
  else
  {
    IllegalArgument(s,
                    "expected satisfiability/entailment result, "
                    "instead got `%s'",
                    s.c_str());
  }
}

UnknownExplanation Result::getUnknownExplanation() const
{
  Assert(isUnknown()) << "This result is not unknown, so the reason for "
                         "being unknown cannot be inquired of it";
  return d_unknownExplanation;
}

bool Result::operator==(const Result& r) const {
  return d_status == r.d_status
         && (d_status != UNKNOWN
             || d_unknownExplanation == r.d_unknownExplanation);
}

bool Result::operator!=(const Result& r) const { return !(*this == r); }

string Result::toString() const {
  stringstream ss;
  ss << *this;
  return ss.str();
}

ostream& operator<<(ostream& out, enum Result::Status s)
{
  switch (s) {
    case Result::NONE: out << "NONE"; break;
    case Result::UNSAT:
      out << "UNSAT";
      break;
    case Result::SAT:
      out << "SAT";
      break;
    case Result::UNKNOWN: out << "UNKNOWN"; break;
    default: Unhandled() << s;
  }
  return out;
}

ostream& operator<<(ostream& out, const Result& r) {
  Language language = options::ioutils::getOutputLanguage(out);
  switch (language) {
    case Language::LANG_SYGUS_V2: r.toStreamSmt2(out); break;
    default:
      if (language::isLangSmt2(language))
      {
        r.toStreamSmt2(out);
      }
      else
      {
        r.toStreamDefault(out);
      }
  };
  return out;
}

void Result::toStreamDefault(std::ostream& out) const {
  switch (d_status)
  {
    case Result::NONE: out << "none"; break;
    case Result::UNSAT: out << "unsat"; break;
    case Result::SAT: out << "sat"; break;
    case Result::UNKNOWN:
      out << "unknown";
      if (getUnknownExplanation() != UnknownExplanation::UNKNOWN_REASON)
      {
        out << " (" << getUnknownExplanation() << ")";
      }
      break;
    default: out << "???"; break;
  }
}

void Result::toStreamSmt2(ostream& out) const {
  if (d_status == Result::UNKNOWN)
  {
    // to avoid printing the reason
    out << "unknown";
    return;
  }
  toStreamDefault(out);
}

}  // namespace cvc5::internal
