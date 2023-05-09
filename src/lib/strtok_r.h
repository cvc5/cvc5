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
 * Replacement for strtok_r() for systems without it (like Win32).
 */

#include "cvc5_private.h"

#ifndef CVC5__LIB__STRTOK_R_H
#define CVC5__LIB__STRTOK_R_H

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
#endif /* CVC5__LIB__STRTOK_R_H */
