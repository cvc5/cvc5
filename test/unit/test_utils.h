/*********************                                                        */
/*! \file test_utils.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for testing.
 **
 **/

#include <sys/wait.h>
#include <unistd.h>

/**
 * Use TS_UTILS_EXPECT_ABORT if you expect the expression to abort() when a
 * CVC4_CHECK or CVC4_DCHECK is triggered.
 */
#define TS_UTILS_EXPECT_ABORT(expr) \
  do                                \
  {                                 \
    int32_t status;                 \
    if (fork())                     \
    {                               \
      wait(&status);                \
    }                               \
    else                            \
    {                               \
      expr;                         \
      exit(EXIT_SUCCESS);           \
    }                               \
    TS_ASSERT(WIFSIGNALED(status)); \
  } while (0)
