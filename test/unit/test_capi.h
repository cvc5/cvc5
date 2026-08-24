/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Common header for cvc5 C API unit tests.
 */

#ifndef CVC5__TEST__UNIT__TEST_CAPI_H
#define CVC5__TEST__UNIT__TEST_CAPI_H

#include <cvc5/c/cvc5.h>

#include <string>

#include "gtest/gtest.h"

/**
 * Assert that the expression `stmt` triggers a cvc5 C API error whose message
 * contains the substring `msg`.
 *
 * The cvc5 C API does not terminate the process on error. Instead, it records
 * the error in thread-local state, which can be queried via `cvc5_has_error()`
 * and `cvc5_get_error_message()`. This macro is the C API counterpart of
 * gtest's `ASSERT_DEATH`: it evaluates `stmt` and checks that it set the error
 * state to a message containing `msg`. Both `stmt` and `msg` are evaluated
 * exactly once.
 */
#define ASSERT_CVC5_ERROR(stmt, msg)                                      \
  do                                                                      \
  {                                                                       \
    const std::string cvc5_expected_msg{(msg)};                           \
    cvc5_reset_error();                                                   \
    (void)(stmt);                                                         \
    const std::string cvc5_actual_msg{cvc5_get_error_message()};          \
    ASSERT_TRUE(cvc5_has_error())                                         \
        << "expected an error containing '" << cvc5_expected_msg          \
        << "' but no error occurred";                                     \
    ASSERT_NE(cvc5_actual_msg.find(cvc5_expected_msg), std::string::npos) \
        << "expected error message to contain '" << cvc5_expected_msg     \
        << "' but got '" << cvc5_actual_msg << "'";                       \
  } while (false)

#endif
