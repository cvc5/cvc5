/*********************                                                        */
/*! \file cvc4cpp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Check macros for the CVC5 C++ API.
 **
 ** These macros implement guards for the CVC5 C++ API functions.
 **/

#include "cvc4_public.h"

#ifndef CVC5__API__CHECKS_H
#define CVC5__API__CHECKS_H

namespace cvc4 {
namespace api {

/* -------------------------------------------------------------------------- */
/* Basic check macros.                                                        */
/* -------------------------------------------------------------------------- */

/**
 * The base check macro.
 * Throws a CVC4ApiException if 'cond' is false.
 */
#define CVC4_API_CHECK(cond) \
  CVC4_PREDICT_TRUE(cond)    \
  ? (void)0 : OstreamVoider() & CVC4ApiExceptionStream().ostream()

/**
 * The base check macro for throwing recoverable exceptions.
 * Throws a CVC4RecoverableApiException if 'cond' is false.
 */
#define CVC4_API_RECOVERABLE_CHECK(cond) \
  CVC4_PREDICT_TRUE(cond)                \
  ? (void)0 : OstreamVoider() & CVC4ApiRecoverableExceptionStream().ostream()

/* -------------------------------------------------------------------------- */
/* Not null checks.                                                           */
/* -------------------------------------------------------------------------- */

/** Check it 'this' is not a null object. */
#define CVC4_API_CHECK_NOT_NULL                     \
  CVC4_API_CHECK(!isNullHelper())                   \
      << "Invalid call to '" << __PRETTY_FUNCTION__ \
      << "', expected non-null object";

/** Check if given argument is not a null object. */
#define CVC4_API_ARG_CHECK_NOT_NULL(arg) \
  CVC4_API_CHECK(!arg.isNull()) << "Invalid null argument for '" << #arg << "'";

/** Check if given argument is not a null pointer. */
#define CVC4_API_ARG_CHECK_NOT_NULLPTR(arg) \
  CVC4_API_CHECK(arg != nullptr)            \
      << "Invalid null argument for '" << #arg << "'";
/**
 * Check if given argument at given index in container 'args' is not a null
 * object.
 */
#define CVC4_API_ARG_AT_INDEX_CHECK_NOT_NULL(what, arg, args, idx)      \
  CVC4_API_CHECK(!arg.isNull()) << "Invalid null " << (what) << " in '" \
                                << #args << "' at index " << (idx);

/* -------------------------------------------------------------------------- */
/* Kind checks.                                                               */
/* -------------------------------------------------------------------------- */

/** Check if given kind is a valid kind. */
#define CVC4_API_KIND_CHECK(kind)     \
  CVC4_API_CHECK(isDefinedKind(kind)) \
      << "Invalid kind '" << kindToString(kind) << "'";

/**
 * Check if given kind is a valid kind.
 * Creates a stream to provide a message that identifies what kind was expected
 * if given kind is invalid.
 */
#define CVC4_API_KIND_CHECK_EXPECTED(cond, kind) \
  CVC4_PREDICT_TRUE(cond)                        \
  ? (void)0                                      \
  : OstreamVoider()                              \
          & CVC4ApiExceptionStream().ostream()   \
                << "Invalid kind '" << kindToString(kind) << "', expected "

/* -------------------------------------------------------------------------- */
/* Argument checks.                                                           */
/* -------------------------------------------------------------------------- */

/**
 * Check condition 'cond' for given argument 'arg'.
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false and throws a non-recoverable exception.
 */
#define CVC4_API_ARG_CHECK_EXPECTED(cond, arg)                      \
  CVC4_PREDICT_TRUE(cond)                                           \
  ? (void)0                                                         \
  : OstreamVoider()                                                 \
          & CVC4ApiExceptionStream().ostream()                      \
                << "Invalid argument '" << arg << "' for '" << #arg \
                << "', expected "

/**
 * Check condition 'cond' for given argument 'arg'.
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false and throws a recoverable exception.
 */
#define CVC4_API_RECOVERABLE_ARG_CHECK_EXPECTED(cond, arg)          \
  CVC4_PREDICT_TRUE(cond)                                           \
  ? (void)0                                                         \
  : OstreamVoider()                                                 \
          & CVC4ApiRecoverableExceptionStream().ostream()           \
                << "Invalid argument '" << arg << "' for '" << #arg \
                << "', expected "

/**
 * Check condition 'cond' for given argument 'arg'.
 * Provides a more specific error message than CVC4_API_ARG_CHECK_EXPECTED,
 * it identifies that this check is a size check.
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false and throws a recoverable exception.
 */
#define CVC4_API_ARG_SIZE_CHECK_EXPECTED(cond, arg) \
  CVC4_PREDICT_TRUE(cond)                           \
  ? (void)0                                         \
  : OstreamVoider()                                 \
          & CVC4ApiExceptionStream().ostream()      \
                << "Invalid size of argument '" << #arg << "', expected "

/**
 * Check condition 'cond' for given argument 'arg' at given index.
 * Argument 'what' identifies what is being checked (e.g., "term").
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false.
 * Usage:
 *   CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(<condition>, "what", <arg>, <idx>)
 *     << "message";
 */
#define CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(cond, what, arg, idx)           \
  CVC4_PREDICT_TRUE(cond)                                                    \
  ? (void)0                                                                  \
  : OstreamVoider()                                                          \
          & CVC4ApiExceptionStream().ostream()                               \
                << "Invalid " << what << " '" << arg << "' at index " << idx \
                << ", expected "

/* -------------------------------------------------------------------------- */
/* Solver checks.                                                             */
/* -------------------------------------------------------------------------- */

/** Sort checks for member functions of class Solver. */
#define CVC4_API_SOLVER_CHECK_SORT(sort) \
  CVC4_API_CHECK(this == sort.d_solver)  \
      << "Given sort is not associated with this solver";

/** Term checks for member functions of class Solver. */
#define CVC4_API_SOLVER_CHECK_TERM(term) \
  CVC4_API_CHECK(this == term.d_solver)  \
      << "Given term is not associated with this solver";

/** Op checks for member functions of class Solver. */
#define CVC4_API_SOLVER_CHECK_OP(op)  \
  CVC4_API_CHECK(this == op.d_solver) \
      << "Given operator is not associated with this solver";

}  // namespace api
}  // namespace cvc4
#endif
