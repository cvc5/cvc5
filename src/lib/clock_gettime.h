/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Replacement for clock_gettime() for systems without it (Windows).
 */

#include "cvc5_private_library.h"

#ifndef CVC5__LIB__CLOCK_GETTIME_H
#define CVC5__LIB__CLOCK_GETTIME_H

#include "lib/replacements.h"

#ifdef HAVE_CLOCK_GETTIME

/* it should be available from <time.h> */
#include <time.h>

#else /* HAVE_CLOCK_GETTIME */

/* otherwise, we have to define it */

#if defined(__WIN32__) && !defined(_W64)

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

struct timespec {
  uint64_t tv_sec;
  int32_t tv_nsec;
};/* struct timespec */

#ifdef __cplusplus
}/* extern "C" */
#endif /* __cplusplus */

#else /* !__WIN32__ || _W64 */

/* get timespec from <time.h> */
#include <time.h>

#endif /* __WIN32__ && !_W64 */

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

struct timespec;

typedef enum {
  CLOCK_REALTIME,
  CLOCK_MONOTONIC,
  CLOCK_REALTIME_HR,
  CLOCK_MONOTONIC_HR
} clockid_t;

long clock_gettime(clockid_t which_clock, struct timespec* tp);

#ifdef __cplusplus
}/* extern "C" */
#endif /* __cplusplus */

#endif /* HAVE_CLOCK_GETTIME */
#endif /*CVC5__LIB__CLOCK_GETTIME_H */
