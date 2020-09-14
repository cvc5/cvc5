/*********************                                                        */
/*! \file smt_mode.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Enumeration type for the mode of an SmtEngine.
 **/

#include "cvc4_public.h"

#ifndef CVC4__SMT__SMT_MODE_H
#define CVC4__SMT__SMT_MODE_H

#include <iosfwd>

namespace CVC4 {

/**
 * The mode of the solver, which is an extension of Figure 4.1 on
 * page 52 of the SMT-LIB version 2.6 standard
 * http://smtlib.cs.uiowa.edu/papers/smt-lib-reference-v2.6-r2017-07-18.pdf
 */
enum class SmtMode
{
  // the initial state of the solver
  START,
  // normal state of the solver, after assert/push/pop/declare/define
  ASSERT,
  // immediately after a check-sat returning "sat"
  SAT,
  // immediately after a check-sat returning "unknown"
  SAT_UNKNOWN,
  // immediately after a check-sat returning "unsat"
  UNSAT,
  // immediately after a successful call to get-abduct
  ABDUCT,
  // immediately after a successful call to get-interpol
  INTERPOL
};
/**
 * Writes a SmtMode to a stream.
 *
 * @param out The stream to write to
 * @param m The mode to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, SmtMode m);

}  // namespace CVC4

#endif
