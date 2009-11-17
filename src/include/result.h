/*********************                                           -*- C++ -*-  */
/** result.h
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/

#ifndef __CVC4_RESULT_H
#define __CVC4_RESULT_H

namespace CVC4 {

// TODO: perhaps best to templatize Result on its Kind (SAT/Validity),
// but this requires doing the same for Prover and needs discussion.

// TODO: subclass to provide models, etc.  This is really just
// intended as a three-valued response code.

/**
 * Three-valued, immutable SMT result, with optional explanation.
 */
class Result {
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
  enum { TYPE_SAT, TYPE_VALIDITY } d_which;

public:
  Result(enum SAT);
  Result(enum Validity);

  enum SAT isSAT();
  enum Validity isValid();
  enum UnknownExplanation whyUnknown();

};/* class Result */

}/* CVC4 namespace */

#endif /* __CVC4_RESULT_H */
