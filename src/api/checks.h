/*********************                                                        */
/*! \file checks.h
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

#ifndef CVC4__API__CHECKS_H
#define CVC4__API__CHECKS_H

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
 * Check condition 'cond' for the argument at given index in container 'args'.
 * Argument 'what' identifies what is being checked (e.g., "term").
 * Creates a stream to provide a message that identifies what was expected to
 * hold if condition is false.
 * Usage:
 *   CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
 *     <condition>, "what", <container>, <idx>) << "message";
 */
#define CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(cond, what, args, idx)          \
  CVC4_PREDICT_TRUE(cond)                                                    \
  ? (void)0                                                                  \
  : OstreamVoider()                                                          \
          & CVC4ApiExceptionStream().ostream()                               \
                << "Invalid " << (what) << " in '" << #args << "' at index " \
                << (idx) << ", expected "

/* -------------------------------------------------------------------------- */
/* Solver checks.                                                             */
/* -------------------------------------------------------------------------- */

/**
 * Solver check for member functions of classes other than class Solver.
 * Check if given solver matches the solver object this object is associated
 * with.
 */
#define CVC4_API_ARG_CHECK_SOLVER(what, arg)                              \
  CVC4_API_CHECK(this->d_solver == arg.d_solver)                          \
      << "Given " << (what) << " is not associated with the solver this " \
      << "object is associated with";

/* -------------------------------------------------------------------------- */
/* Sort checks.                                                               */
/* -------------------------------------------------------------------------- */

/**
 * Sort check for member functions of classes other than class Solver.
 * Check if given sort is not null and associated with the solver object this
 * object is associated with.
 */
#define CVC4_API_CHECK_SORT(sort)            \
  do                                         \
  {                                          \
    CVC4_API_ARG_CHECK_NOT_NULL(sort);       \
    CVC4_API_ARG_CHECK_SOLVER("sort", sort); \
  } while (0)

/**
 * Sort check for member functions of classes other than class Solver.
 * Check if each sort in the given container of sorts is not null and
 * associated with the solver object this object is associated with.
 */
#define CVC4_API_CHECK_SORTS(sorts)                                         \
  do                                                                        \
  {                                                                         \
    size_t i = 0;                                                           \
    for (const auto& s : sorts)                                             \
    {                                                                       \
      CVC4_API_ARG_AT_INDEX_CHECK_NOT_NULL("sort", s, sorts, i);            \
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == s.d_solver, "sort", sorts, i)                   \
          << "a sort associated with the solver this object is associated " \
             "with";                                                        \
      i += 1;                                                               \
    }                                                                       \
  } while (0)

/* -------------------------------------------------------------------------- */
/* Term checks.                                                               */
/* -------------------------------------------------------------------------- */

/**
 * Term check for member functions of classes other than class Solver.
 * Check if given term is not null and associated with the solver object this
 * object is associated with.
 */
#define CVC4_API_CHECK_TERM(term)            \
  do                                         \
  {                                          \
    CVC4_API_ARG_CHECK_NOT_NULL(term);       \
    CVC4_API_ARG_CHECK_SOLVER("term", term); \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term in the given container of terms is not null and
 * associated with the solver object this object is associated with.
 */
#define CVC4_API_CHECK_TERMS(terms)                                         \
  do                                                                        \
  {                                                                         \
    size_t i = 0;                                                           \
    for (const auto& s : terms)                                             \
    {                                                                       \
      CVC4_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", s, terms, i);            \
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == s.d_solver, "term", terms, i)                   \
          << "a term associated with the solver this object is associated " \
             "with";                                                        \
      i += 1;                                                               \
    }                                                                       \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term and sort in the given map (which maps terms to sorts) is
 * not null and associated with the solver object this object is associated
 * with.
 */
#define CVC4_API_CHECK_TERMS_MAP(map)                                       \
  do                                                                        \
  {                                                                         \
    size_t i = 0;                                                           \
    for (const auto& p : map)                                               \
    {                                                                       \
      CVC4_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", p.first, map, i);        \
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == p.first.d_solver, "term", map, i)               \
          << "a term associated with the solver this object is associated " \
             "with";                                                        \
      CVC4_API_ARG_AT_INDEX_CHECK_NOT_NULL("sort", p.second, map, i);       \
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(                                 \
          this->d_solver == p.second.d_solver, "sort", map, i)              \
          << "a sort associated with the solver this object is associated " \
             "with";                                                        \
      i += 1;                                                               \
    }                                                                       \
  } while (0)

/**
 * Term check for member functions of classes other than class Solver.
 * Check if each term in the given container is not null, associated with the
 * solver object this object is associated with, and of the given sort.
 */
#define CVC4_API_CHECK_TERMS_WITH_SORT(terms, sort)                            \
  do                                                                           \
  {                                                                            \
    size_t i = 0;                                                              \
    for (const auto& t : terms)                                                \
    {                                                                          \
      CVC4_API_ARG_AT_INDEX_CHECK_NOT_NULL("term", t, terms, i);               \
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(                                    \
          this->d_solver == t.d_solver, "term", terms, i)                      \
          << "a term associated with the solver this object is associated "    \
             "with";                                                           \
      CVC4_API_CHECK(t.getSort() == sort)                                      \
          << "Expected term with sort " << sort << " at index " << i << " in " \
          << #terms;                                                           \
      i += 1;                                                                  \
    }                                                                          \
  } while (0)

/* -------------------------------------------------------------------------- */
/* DatatypeDecl checks.                                                       */
/* -------------------------------------------------------------------------- */

/**
 * DatatypeDecl check for member functions of classes other than class Solver.
 * Check if given datatype declaration is not null and associated with the
 * solver object this DatatypeDecl object is associated with.
 */
#define CVC4_API_CHECK_DTDECL(decl)                          \
  do                                                         \
  {                                                          \
    CVC4_API_ARG_CHECK_NOT_NULL(decl);                       \
    CVC4_API_ARG_CHECK_SOLVER("datatype declaration", decl); \
  } while (0)

/* -------------------------------------------------------------------------- */
/* Checks for class Solver.                                                   */
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
