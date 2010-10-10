/*********************                                                        */
/*! \file result.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
#include "util/Assert.h"

using namespace std;

namespace CVC4 {

Result::Result(const string& instr) :
  d_sat(SAT_UNKNOWN),
  d_validity(VALIDITY_UNKNOWN),
  d_which(TYPE_NONE),
  d_unknownExplanation(UNKNOWN_REASON) {
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
  } else if(s == "unknown") {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
  } else if(s == "incomplete") {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = INCOMPLETE;
  } else if(s == "timeout") {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = TIMEOUT;
  } else if(s == "memout") {
    d_which = TYPE_SAT;
    d_sat = SAT_UNKNOWN;
    d_unknownExplanation = MEMOUT;
  } else {
    IllegalArgument(s, "expected satisfiability/validity result, "
                    "instead got `%s'", s.c_str());
  }
}

bool Result::operator==(const Result& r) const {
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

Result Result::asSatisfiabilityResult() const {
  if(d_which == TYPE_SAT) {
    return *this;
  }

  Assert(d_which == TYPE_VALIDITY);

  switch(d_validity) {

  case INVALID:
    return Result(SAT);

  case VALID:
    return Result(UNSAT);

  case VALIDITY_UNKNOWN:
    return Result(SAT_UNKNOWN, d_unknownExplanation);

  default:
    Unhandled(d_validity);
  }
}

Result Result::asValidityResult() const {
  if(d_which == TYPE_VALIDITY) {
    return *this;
  }

  Assert(d_which == TYPE_SAT);

  switch(d_sat) {

  case SAT:
    return Result(INVALID);

  case UNSAT:
    return Result(VALID);

  case SAT_UNKNOWN:
    return Result(VALIDITY_UNKNOWN, d_unknownExplanation);

  default:
    Unhandled(d_sat);
  }
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
  case Result::MEMOUT: out << "MEMOUT"; break;
  case Result::OTHER: out << "OTHER"; break;
  case Result::UNKNOWN_REASON: out << "UNKNOWN_REASON"; break;
  default: Unhandled(e);
  }
  return out;
}

ostream& operator<<(ostream& out, const Result& r) {
  if(r.d_which == Result::TYPE_SAT) {
    switch(r.d_sat) {
    case Result::UNSAT:
      out << "unsat";
      break;
    case Result::SAT:
      out << "sat";
      break;
    case Result::SAT_UNKNOWN:
      out << "unknown";
      if(r.whyUnknown() != Result::UNKNOWN_REASON) {
        out << " (" << r.whyUnknown() << ")";
      }
      break;
    }
  } else {
    switch(r.d_validity) {
    case Result::INVALID:
      out << "invalid";
      break;
    case Result::VALID:
      out << "valid";
      break;
    case Result::VALIDITY_UNKNOWN:
      out << "unknown";
      if(r.whyUnknown() != Result::UNKNOWN_REASON) {
        out << " (" << r.whyUnknown() << ")";
      }
      break;
    }
  }

  return out;
}/* operator<<(ostream&, const Result&) */

}/* CVC4 namespace */
