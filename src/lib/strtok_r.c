/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Replacement for strtok_r() for systems without it (like Win32).
 */

#include "lib/strtok_r.h"

#include <stdio.h>
#include <string.h>

#include "cvc5_private.h"

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */
#ifndef HAVE_STRTOK_R

char* strtok_r(char *str, const char *delim, char **saveptr) {
  if(str == NULL) {
    char* retval = strtok(*saveptr, delim);
    *saveptr = retval + strlen(retval) + 1;
    return retval;
  } else {
    char* retval = strtok(str, delim);
    *saveptr = retval + strlen(retval) + 1;
    return retval;
  }
}

#endif /* ifndef HAVE_STRTOK_R */
#ifdef __cplusplus
}/* extern "C" */
#endif /* __cplusplus */
