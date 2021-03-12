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

#ifndef CVC5__API__CVC5_CHECKS_H
#define CVC5__API__CVC5_CHECKS_H

namespace cvc4 {
namespace api {

/**
 * The base check macro.
 * Throws a CVC4ApiException if 'cond' is false.
 */
#define CVC4_API_CHECK(cond) \
  CVC4_PREDICT_TRUE(cond)    \
  ? (void)0 : OstreamVoider() & CVC4ApiExceptionStream().ostream()

/** Check if given argument is not null. */
#define CVC4_API_ARG_CHECK_NOT_NULL(arg) \
  CVC4_API_CHECK(!arg.isNull()) << "Invalid null argument for '" << #arg << "'";

/** Check if given argument at given index in container 'args' is not null. */
#define CVC4_API_ARG_AT_INDEX_CHECK_NOT_NULL(what, arg, args, idx)      \
  CVC4_API_CHECK(!arg.isNull()) << "Invalid null " << (what) << " in '" \
                                << #args << "' at index " << (idx);

/**
 * Check condition 'cond' for given argument at given index in container 'args'.
 * Argument 'what' identifies what is being checked (e.g., "term").
 * Usage:
 *   CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(
 *     <condition>, "what", <container>, <idx>)
 *     << "message that identifies what was expected to hold";
 */
#define CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(cond, what, args, idx)          \
  CVC4_PREDICT_TRUE(cond)                                                    \
  ? (void)0                                                                  \
  : OstreamVoider()                                                          \
          & CVC4ApiExceptionStream().ostream()                               \
                << "Invalid " << (what) << " in '" << #args << "' at index " \
                << (idx) << ", expected "

/**
 * Guard for member functions of class Sort.
 * Check if given sort is not null and associated with the solver object this
 * Sort object is associated with.
 */
#define CVC4_API_SORT_CHECK_SORT(sort)                                  \
  do                                                                    \
  {                                                                     \
    CVC4_API_ARG_CHECK_NOT_NULL(sort);                                  \
    CVC4_API_CHECK(this->d_solver == sort.d_solver)                     \
        << "Given sort is not associated with the solver this sort is " \
           "associated with";                                           \
  } while (0)

/**
 * Guard for member functions of class Sort.
 * Check if each sort in the given container of sorts is not null and
 * associated with the solver object this Sort object is associated with.
 */
#define CVC4_API_SORT_CHECK_SORTS(sorts)                                       \
  do                                                                           \
  {                                                                            \
    size_t i = 0;                                                              \
    for (const auto& s : sorts)                                                \
    {                                                                          \
      CVC4_API_ARG_AT_INDEX_CHECK_NOT_NULL("sort", s, sorts, i);               \
      CVC4_API_ARG_AT_INDEX_CHECK_EXPECTED(                                    \
          this->d_solver == s.d_solver, "sort", sorts, i)                      \
          << "a sort associated with the solver this sort is associated with"; \
      i += 1;                                                                  \
    }                                                                          \
  } while (0)

#endif
}
}
