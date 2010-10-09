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

#include "cvc4_public.h"

#ifndef __CVC4__RESULT_H
#define __CVC4__RESULT_H

namespace CVC4 {

// TODO: perhaps best to templatize Result on its Kind (SAT/Validity),
// but this requires doing the same for Prover and needs discussion.

// TODO: subclass to provide models, etc.  This is really just
// intended as a three-valued response code.

/**
 * Three-valued, immutable SMT result, with optional explanation.
 */
class CVC4_PUBLIC Result {
public:
  enum SAT {
    UNSAT = 0,
    SAT = 1,
    SAT_UNKNOWN = 2
  };

  enum Validity {
    INVALID = 0,
    VALID = 1,
    VALIDITY_UNKNOWN = 2
  };

  enum UnknownExplanation {
    REQUIRES_FULL_CHECK,
    INCOMPLETE,
    TIMEOUT,
    BAIL,
    OTHER
  };

private:
  enum SAT      d_sat;
  enum Validity d_validity;
  enum { TYPE_SAT, TYPE_VALIDITY, TYPE_NONE } d_which;

  friend std::ostream& CVC4::operator<<(std::ostream& out, Result r);

public:
  Result() :
    d_sat(SAT_UNKNOWN),
    d_validity(VALIDITY_UNKNOWN),
    d_which(TYPE_NONE) {
  }
  Result(enum SAT s) :
    d_sat(s),
    d_validity(VALIDITY_UNKNOWN),
    d_which(TYPE_SAT) {
  }
  Result(enum Validity v) :
    d_sat(SAT_UNKNOWN),
    d_validity(v),
    d_which(TYPE_VALIDITY) {
  }

  enum SAT isSAT() {
    return d_which == TYPE_SAT ? d_sat : SAT_UNKNOWN;
  }
  enum Validity isValid() {
    return d_which == TYPE_VALIDITY ? d_validity : VALIDITY_UNKNOWN;
  }
  enum UnknownExplanation whyUnknown();

  inline bool operator==(Result r) {
    if(d_which != r.d_which) {
      return false;
    }
    if(d_which == TYPE_SAT) {
      return d_sat == r.d_sat;
    }
    if(d_which == TYPE_VALIDITY) {
      return d_validity == r.d_validity;
    }
    return false;
  }
  inline bool operator!=(Result r) {
    return !(*this == r);
  }
  inline Result asSatisfiabilityResult() const;
  inline Result asValidityResult() const;

};/* class Result */

inline Result Result::asSatisfiabilityResult() const {
  if(d_which == TYPE_SAT) {
    return *this;
  }

  switch(d_validity) {

  case INVALID:
    return Result(SAT);

  case VALID:
    return Result(UNSAT);

  case VALIDITY_UNKNOWN:
    return Result(SAT_UNKNOWN);

  default:
    Unhandled(d_validity);
  }
}

inline Result Result::asValidityResult() const {
  if(d_which == TYPE_VALIDITY) {
    return *this;
  }

  switch(d_sat) {

  case SAT:
    return Result(INVALID);

  case UNSAT:
    return Result(VALID);

  case SAT_UNKNOWN:
    return Result(VALIDITY_UNKNOWN);

  default:
    Unhandled(d_sat);
  }
}

inline std::ostream& operator<<(std::ostream& out, Result r) {
  if(r.d_which == Result::TYPE_SAT) {
    switch(r.d_sat) {
    case Result::UNSAT: out << "UNSAT"; break;
    case Result::SAT: out << "SAT"; break;
    case Result::SAT_UNKNOWN: out << "SAT_UNKNOWN"; break;
    }
  } else {
    switch(r.d_validity) {
    case Result::INVALID: out << "INVALID"; break;
    case Result::VALID: out << "VALID"; break;
    case Result::VALIDITY_UNKNOWN: out << "VALIDITY_UNKNOWN"; break;
    }
  }

  return out;
}

}/* CVC4 namespace */

#endif /* __CVC4__RESULT_H */
