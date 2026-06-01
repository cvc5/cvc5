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
 * Assert that statement `stmt` triggers a cvc5 C API error whose message
 * contains the substring `msg`.
 *
 * The cvc5 C API does not terminate the process on error. Instead, it records
 * the error in thread-local state, which can be queried via `cvc5_has_error()`
 * and `cvc5_get_error_message()`. This macro is the C API counterpart of
 * gtest's `ASSERT_DEATH`: it runs `stmt` and checks that it set the error
 * state to a message containing `msg`.
 */
#define ASSERT_CVC5_ERROR(stmt, msg)                                           \
  do                                                                           \
  {                                                                            \
    cvc5_reset_error();                                                        \
    (void)(stmt);                                                              \
    ASSERT_TRUE(cvc5_has_error()) << "expected an error containing '" << (msg) \
                                  << "' but no error occurred";                \
    ASSERT_NE(std::string(cvc5_get_error_message()).find(msg),                 \
              std::string::npos)                                               \
        << "expected error message to contain '" << (msg) << "' but got '"     \
        << cvc5_get_error_message() << "'";                                    \
  } while (false)

#endif
