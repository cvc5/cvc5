/*********************                                           -*- C++ -*-  */
/** result.h
 ** This file is part of the CVC4 prototype.
 **
 ** The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
  enum {
    UNSAT = 0,
    SAT = 1,
    UNKNOWN = 2
  } SAT;

  enum {
    INVALID = 0,
    VALID = 1,
    UNKNOWN = 2
  } Validity;

  enum {
    REQUIRES_FULL_CHECK,
    INCOMPLETE,
    TIMEOUT,
    BAIL,
    OTHER
  } UnknownExplanation;

private:
  SAT      d_sat;
  Validity d_validity;
  enum { SAT, VALIDITY } d_which;

public:
  Result(SAT);
  Result(Validity);

  SAT isSAT();
  Validity isValid();
  UnknownExplanation whyUnknown();

};/* class Result */

}/* CVC4 namespace */
