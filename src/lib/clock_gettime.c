/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King, Mathias Preiner
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

// #warning "TODO(taking): Make lib/clock_gettime.h cvc5_private.h again."

#include "lib/clock_gettime.h"

#ifndef HAVE_CLOCK_GETTIME

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

#ifdef __WIN32__

#include <time.h>
#include <windows.h>

long clock_gettime(clockid_t which_clock, struct timespec* tp) {
  if(tp != NULL) {
    FILETIME ft;
    GetSystemTimeAsFileTime(&ft);
    uint64_t nanos = ((((uint64_t)ft.dwHighDateTime) << 32) | ft.dwLowDateTime) * 100;
    tp->tv_sec = nanos / 1000000000ul;
    tp->tv_nsec = nanos % 1000000000ul;
  }
  return 0;
}

#endif /* closing #ifdef __WIN32__ */

#ifdef __cplusplus
}/* extern "C" */
#endif /* __cplusplus */

#endif /* HAVE_CLOCK_GETTIME */
