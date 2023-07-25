/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Enumeration type for the mode of an SolverEngine.
 */

#include "cvc5_public.h"

#ifndef CVC5__SMT__SMT_MODE_H
#define CVC5__SMT__SMT_MODE_H

#include <iosfwd>

namespace cvc5::internal {

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
  // immediately after a successful call to get-interpolant
  INTERPOL,
  // immediately after a successful call to check-synth or check-synth-next
  SYNTH,
  // immediately after a successful call to find-synth or find-synth-next
  FIND_SYNTH
};
/**
 * Writes a SmtMode to a stream.
 *
 * @param out The stream to write to
 * @param m The mode to write to the stream
 * @return The stream
 */
std::ostream& operator<<(std::ostream& out, SmtMode m);

}  // namespace cvc5::internal

#endif
