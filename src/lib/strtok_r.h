/*********************                                                        */
/*! \file strtok_r.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Replacement for strtok_r() for systems without it (like Win32)
 **
 ** Replacement for strtok_r() for systems without it (like Win32).
 **/

#include "cvc4_private.h"

#ifndef CVC4__LIB__STRTOK_R_H
#define CVC4__LIB__STRTOK_R_H

#ifdef HAVE_STRTOK_R

// available in string.h
#include <string.h>

#else /* ! HAVE_STRTOK_R */

#include "lib/replacements.h"

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

char* strtok_r(char *str, const char *delim, char **saveptr);

#ifdef __cplusplus
}/* extern "C" */
#endif /* __cplusplus */

#endif /* HAVE_STRTOK_R */
#endif /* CVC4__LIB__STRTOK_R_H */
