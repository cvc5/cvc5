/*********************                                                        */
/*! \file result.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Aina Niemetz, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Encapsulation of the result of a query.
 **
 ** Encapsulation of the result of a query.
 **/
#include "util/result.h"

#include <algorithm>
#include <cctype>
#include <iostream>
#include <string>

#include "base/check.h"
#include "options/set_language.h"

using namespace std;

namespace CVC4 {

Result::Result()
    : d_sat(SAT_UNKNOWN),
      d_entailment(ENTAILMENT_UNKNOWN),
      d_which(TYPE_NONE),
      d_unknownExplanation(UNKNOWN_REASON),
      d_inputName("")
{
}

Result::Result(enum Sat s, std::string inputName)
    : d_sat(s),
      d_entailment(ENTAILMENT_UNKNOWN),
      d_which(TYPE_SAT),
      d_unknownExplanation(UNKNOWN_REASON),
      d_inputName(inputName)
{
  PrettyCheckArgument(s != SAT_UNKNOWN,
                      "Must provide a reason for satisfiability being unknown");
}

Result::Result(enum Entailment e, std::string inputName)
    : d_sat(SAT_UNKNOWN),
      d_entailment(e),
      d_which(TYPE_ENTAILMENT),
      d_unknownExplanation(UNKNOWN_REASON),
      d_inputName(inputName)
{
  PrettyCheckArgument(e != ENTAILMENT_UNKNOWN,
                      "Must provide a reason for entailment being unknown");
}

Result::Result(enum Sat s,
               enum UnknownExplanation unknownExplanation,
               std::string inputName)
    : d_sat(s),
      d_entailment(ENTAILMENT_UNKNOWN),
      d_which(TYPE_SAT),
      d_unknownExplanation(unknownExplanation),
      d_inputName(inputName)
{
  PrettyCheckArgument(s == SAT_UNKNOWN,
                      "improper use of unknown-result constructor");
}

Result::Result(enum Entailment e,
               enum UnknownExplanation unknownExplanation,
               std::string inputName)
    : d_sat(SAT_UNKNOWN),
      d_entailment(e),
      d_which(TYPE_ENTAILMENT),
      d_unknownExplanation(unknownExplanation),
      d_inputName(inputName)
{
  PrettyCheckArgument(e == ENTAILMENT_UNKNOWN,
                      "improper use of unknown-result constructor");
}

Result::Result(const std::string& instr, std::string inputName)
    : d_sat(SAT_UNKNOWN),
      d_entailment(ENTAILMENT_UNKNOWN),
      d_which(TYPE_NONE),
      d_unknownExplanation(UNKNOWN_REASON),
      d_inputName(inputName)
{
  string s = instr;
  transform(s.begin(), s.end(), s.begin(), ::tolower);
  if (s == "sat" || s == "satisfiable") {
    d_which = TYPE_SAT;
    d_sat = SAT;
  } else if (s == "unsat" || s == "unsatisfiable") {
    d_which = TYPE_SAT;
    d_sat = UNSAT;
  }
  else if (s == "entailed")
  {
    d_which = TYPE_ENTAILMENT;
    d_entailment = ENTAILED;
  }
  else if (s == "not_entailed")
  {
    d_which = TYPE_ENTAILMENT;
    d_entailment = NOT_ENTAILED;
  }
  else if (s == "incomplete")
  {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = INCOMPLETE;
  }
  else if (s == "timeout")
  {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = TIMEOUT;
  }
  else if (s == "resourceout")
  {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = RESOURCEOUT;
  }
  else if (s == "memout")
  {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = MEMOUT;
  }
  else if (s == "interrupted")
  {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = INTERRUPTED;
  }
  else if (s.size() >= 7 && s.compare(0, 7, "unknown") == 0)
  {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
  }
  else
  {
    IllegalArgument(s,
                    "expected satisfiability/entailment result, "
                    "instead got `%s'",
                    s.c_str());
  }
}

Result::UnknownExplanation Result::whyUnknown() const {
  PrettyCheckArgument(isUnknown(), this,
                      "This result is not unknown, so the reason for "
                      "being unknown cannot be inquired of it");
  return d_unknownExplanation;
}

bool Result::operator==(const Result& r) const {
  if (d_which != r.d_which) {
    return false;
  }
  if (d_which == TYPE_SAT) {
    return d_sat == r.d_sat && (d_sat != SAT_UNKNOWN ||
                                d_unknownExplanation == r.d_unknownExplanation);
  }
  if (d_which == TYPE_ENTAILMENT)
  {
    return d_entailment == r.d_entailment
           && (d_entailment != ENTAILMENT_UNKNOWN
               || d_unknownExplanation == r.d_unknownExplanation);
  }
  return false;
}

bool operator==(enum Result::Sat sr, const Result& r) { return r == sr; }

bool operator==(enum Result::Entailment e, const Result& r) { return r == e; }
bool operator!=(enum Result::Sat s, const Result& r) { return !(s == r); }
bool operator!=(enum Result::Entailment e, const Result& r)
{
  return !(e == r);
}

Result Result::asSatisfiabilityResult() const {
  if (d_which == TYPE_SAT) {
    return *this;
  }

  if (d_which == TYPE_ENTAILMENT)
  {
    switch (d_entailment)
    {
      case NOT_ENTAILED: return Result(SAT, d_inputName);

      case ENTAILED: return Result(UNSAT, d_inputName);

      case ENTAILMENT_UNKNOWN:
        return Result(SAT_UNKNOWN, d_unknownExplanation, d_inputName);

      default: Unhandled() << d_entailment;
    }
  }

  // TYPE_NONE
  return Result(SAT_UNKNOWN, NO_STATUS, d_inputName);
}

Result Result::asEntailmentResult() const
{
  if (d_which == TYPE_ENTAILMENT)
  {
    return *this;
  }

  if (d_which == TYPE_SAT) {
    switch (d_sat) {
      case SAT: return Result(NOT_ENTAILED, d_inputName);

      case UNSAT: return Result(ENTAILED, d_inputName);

      case SAT_UNKNOWN:
        return Result(ENTAILMENT_UNKNOWN, d_unknownExplanation, d_inputName);

      default: Unhandled() << d_sat;
    }
  }

  // TYPE_NONE
  return Result(ENTAILMENT_UNKNOWN, NO_STATUS, d_inputName);
}

string Result::toString() const {
  stringstream ss;
  ss << *this;
  return ss.str();
}

ostream& operator<<(ostream& out, enum Result::Sat s) {
  switch (s) {
    case Result::UNSAT:
      out << "UNSAT";
      break;
    case Result::SAT:
      out << "SAT";
      break;
    case Result::SAT_UNKNOWN:
      out << "SAT_UNKNOWN";
      break;
    default: Unhandled() << s;
  }
  return out;
}

ostream& operator<<(ostream& out, enum Result::Entailment e)
{
  switch (e)
  {
    case Result::NOT_ENTAILED: out << "NOT_ENTAILED"; break;
    case Result::ENTAILED: out << "ENTAILED"; break;
    case Result::ENTAILMENT_UNKNOWN: out << "ENTAILMENT_UNKNOWN"; break;
    default: Unhandled() << e;
  }
  return out;
}

ostream& operator<<(ostream& out, enum Result::UnknownExplanation e) {
  switch (e) {
    case Result::REQUIRES_FULL_CHECK:
      out << "REQUIRES_FULL_CHECK";
      break;
    case Result::INCOMPLETE:
      out << "INCOMPLETE";
      break;
    case Result::TIMEOUT:
      out << "TIMEOUT";
      break;
    case Result::RESOURCEOUT:
      out << "RESOURCEOUT";
      break;
    case Result::MEMOUT:
      out << "MEMOUT";
      break;
    case Result::INTERRUPTED:
      out << "INTERRUPTED";
      break;
    case Result::NO_STATUS:
      out << "NO_STATUS";
      break;
    case Result::UNSUPPORTED:
      out << "UNSUPPORTED";
      break;
    case Result::OTHER:
      out << "OTHER";
      break;
    case Result::UNKNOWN_REASON:
      out << "UNKNOWN_REASON";
      break;
    default: Unhandled() << e;
  }
  return out;
}

ostream& operator<<(ostream& out, const Result& r) {
  r.toStream(out, language::SetLanguage::getLanguage(out));
  return out;
} /* operator<<(ostream&, const Result&) */

void Result::toStreamDefault(std::ostream& out) const {
  if (getType() == Result::TYPE_SAT) {
    switch (isSat()) {
      case Result::UNSAT:
        out << "unsat";
        break;
      case Result::SAT:
        out << "sat";
        break;
      case Result::SAT_UNKNOWN:
        out << "unknown";
        if (whyUnknown() != Result::UNKNOWN_REASON) {
          out << " (" << whyUnknown() << ")";
        }
        break;
    }
  } else {
    switch (isEntailed())
    {
      case Result::NOT_ENTAILED: out << "not_entailed"; break;
      case Result::ENTAILED: out << "entailed"; break;
      case Result::ENTAILMENT_UNKNOWN:
        out << "unknown";
        if (whyUnknown() != Result::UNKNOWN_REASON) {
          out << " (" << whyUnknown() << ")";
        }
        break;
    }
  }
} /* Result::toStreamDefault() */

void Result::toStreamSmt2(ostream& out) const {
  if (getType() == Result::TYPE_SAT && isSat() == Result::SAT_UNKNOWN) {
    out << "unknown";
  } else {
    toStreamDefault(out);
  }
}

void Result::toStreamTptp(std::ostream& out) const {
  out << "% SZS status ";
  if (isSat() == Result::SAT) {
    out << "Satisfiable";
  } else if (isSat() == Result::UNSAT) {
    out << "Unsatisfiable";
  }
  else if (isEntailed() == Result::ENTAILED)
  {
    out << "Theorem";
  }
  else if (isEntailed() == Result::NOT_ENTAILED)
  {
    out << "CounterSatisfiable";
  }
  else
  {
    out << "GaveUp";
  }
  out << " for " << getInputName();
}

void Result::toStream(std::ostream& out, OutputLanguage language) const {
  switch (language) {
    case language::output::LANG_SYGUS_V2: toStreamSmt2(out); break;
    case language::output::LANG_TPTP:
      toStreamTptp(out);
      break;
    default:
      if (language::isOutputLang_smt2(language))
      {
        toStreamSmt2(out);
      }
      else
      {
        toStreamDefault(out);
      }
      break;
  };
}

} /* CVC4 namespace */
