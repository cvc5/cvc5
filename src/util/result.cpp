/*********************                                                        */
/*! \file result.cpp
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Encapsulation of the result of a query.
 **
 ** Encapsulation of the result of a query.
 **/

#include <iostream>
#include <algorithm>
#include <string>
#include <cctype>

#include "util/result.h"
#include "util/cvc4_assert.h"
#include "printer/printer.h"

using namespace std;

namespace CVC4 {

Result::Result(const std::string& instr, std::string inputName) :
  d_sat(SAT_UNKNOWN),
  d_validity(VALIDITY_UNKNOWN),
  d_which(TYPE_NONE),
  d_unknownExplanation(UNKNOWN_REASON),
  d_inputName(inputName) {
  string s = instr;
  transform(s.begin(), s.end(), s.begin(), ::tolower);
  if(s == "sat" || s == "satisfiable") {
    d_which = TYPE_SAT;
    d_sat = SAT;
  } else if(s == "unsat" || s == "unsatisfiable") {
    d_which = TYPE_SAT;
    d_sat = UNSAT;
  } else if(s == "valid") {
    d_which = TYPE_VALIDITY;
    d_validity = VALID;
  } else if(s == "invalid") {
    d_which = TYPE_VALIDITY;
    d_validity = INVALID;
  } else if(s == "incomplete") {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = INCOMPLETE;
  } else if(s == "timeout") {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = TIMEOUT;
  } else if(s == "resourceout") {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = RESOURCEOUT;
  } else if(s == "memout") {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = MEMOUT;
  } else if(s == "interrupted") {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = INTERRUPTED;
  } else if(s.size() >= 7 && s.compare(0, 7, "unknown") == 0) {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
  } else {
    IllegalArgument(s, "expected satisfiability/validity result, "
                    "instead got `%s'", s.c_str());
  }
}

bool Result::operator==(const Result& r) const throw() {
  if(d_which != r.d_which) {
    return false;
  }
  if(d_which == TYPE_SAT) {
    return d_sat == r.d_sat &&
      ( d_sat != SAT_UNKNOWN ||
        d_unknownExplanation == r.d_unknownExplanation );
  }
  if(d_which == TYPE_VALIDITY) {
    return d_validity == r.d_validity &&
      ( d_validity != VALIDITY_UNKNOWN ||
        d_unknownExplanation == r.d_unknownExplanation );
  }
  return false;
}

bool operator==(enum Result::Sat sr, const Result& r) throw() {
  return r == sr;
}

bool operator==(enum Result::Validity vr, const Result& r) throw() {
  return r == vr;
}
bool operator!=(enum Result::Sat s, const Result& r) throw(){
  return !(s == r);
}
bool operator!=(enum Result::Validity v, const Result& r) throw(){
  return !(v == r);
}

Result Result::asSatisfiabilityResult() const throw() {
  if(d_which == TYPE_SAT) {
    return *this;
  }

  if(d_which == TYPE_VALIDITY) {
    switch(d_validity) {

    case INVALID:
      return Result(SAT, d_inputName);

    case VALID:
      return Result(UNSAT, d_inputName);

    case VALIDITY_UNKNOWN:
      return Result(SAT_UNKNOWN, d_unknownExplanation, d_inputName);

    default:
      Unhandled(d_validity);
    }
  }

  // TYPE_NONE
  return Result(SAT_UNKNOWN, NO_STATUS, d_inputName);
}

Result Result::asValidityResult() const throw() {
  if(d_which == TYPE_VALIDITY) {
    return *this;
  }

  if(d_which == TYPE_SAT) {
    switch(d_sat) {

    case SAT:
      return Result(INVALID, d_inputName);

    case UNSAT:
      return Result(VALID, d_inputName);

    case SAT_UNKNOWN:
      return Result(VALIDITY_UNKNOWN, d_unknownExplanation, d_inputName);

    default:
      Unhandled(d_sat);
    }
  }

  // TYPE_NONE
  return Result(VALIDITY_UNKNOWN, NO_STATUS, d_inputName);
}

string Result::toString() const {
  stringstream ss;
  ss << *this;
  return ss.str();
}

ostream& operator<<(ostream& out, enum Result::Sat s) {
  switch(s) {
  case Result::UNSAT: out << "UNSAT"; break;
  case Result::SAT: out << "SAT"; break;
  case Result::SAT_UNKNOWN: out << "SAT_UNKNOWN"; break;
  default: Unhandled(s);
  }
  return out;
}

ostream& operator<<(ostream& out, enum Result::Validity v) {
  switch(v) {
  case Result::INVALID: out << "INVALID"; break;
  case Result::VALID: out << "VALID"; break;
  case Result::VALIDITY_UNKNOWN: out << "VALIDITY_UNKNOWN"; break;
  default: Unhandled(v);
  }
  return out;
}

ostream& operator<<(ostream& out,
                    enum Result::UnknownExplanation e) {
  switch(e) {
  case Result::REQUIRES_FULL_CHECK: out << "REQUIRES_FULL_CHECK"; break;
  case Result::INCOMPLETE: out << "INCOMPLETE"; break;
  case Result::TIMEOUT: out << "TIMEOUT"; break;
  case Result::RESOURCEOUT: out << "RESOURCEOUT"; break;
  case Result::MEMOUT: out << "MEMOUT"; break;
  case Result::INTERRUPTED: out << "INTERRUPTED"; break;
  case Result::NO_STATUS: out << "NO_STATUS"; break;
  case Result::UNSUPPORTED: out << "UNSUPPORTED"; break;
  case Result::OTHER: out << "OTHER"; break;
  case Result::UNKNOWN_REASON: out << "UNKNOWN_REASON"; break;
  default: Unhandled(e);
  }
  return out;
}

ostream& operator<<(ostream& out, const Result& r) {
  Printer::getPrinter(Node::setlanguage::getLanguage(out))->toStream(out, r);
  return out;
}/* operator<<(ostream&, const Result&) */

}/* CVC4 namespace */
