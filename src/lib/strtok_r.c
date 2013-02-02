/*********************                                                        */
/*! \file strtok_r.c
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of CVC4.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Replacement for strtok_r() for systems without it (like Win32)
 **
 ** Replacement for strtok_r() for systems without it (like Win32).
 **/

#include "cvc4_private.h"

#include "lib/strtok_r.h"
#include <stdio.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

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

#ifdef __cplusplus
}/* extern "C" */
#endif /* __cplusplus */
