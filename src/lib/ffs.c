/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Replacement for ffs() for systems without it (like Win32).
 */

#include "lib/ffs.h"

#include "cvc5_private.h"

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */
#ifndef HAVE_FFS

int ffs(int i) {
  long mask = 0x1;
  int pos = 1;
  while(pos <= sizeof(int) * 8) {
    if((mask & i) != 0) {
      return pos;
    }
    ++pos;
    mask <<= 1;
  }
  return 0;
}

#endif /* ifndef HAVE_FFS */
#ifdef __cplusplus
}/* extern "C" */
#endif /* __cplusplus */
