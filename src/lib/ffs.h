/*********************                                                        */
/*! \file ffs.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Replacement for ffs() for systems without it (like Win32)
 **
 ** Replacement for ffs() for systems without it (like Win32).
 **/

#include "cvc4_public.h"

#ifndef __CVC4__LIB__FFS_H
#define __CVC4__LIB__FFS_H

#ifdef HAVE_FFS

// available in strings.h
#include <strings.h>

#else /* ! HAVE_FFS */

#include "lib/replacements.h"

#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

int ffs(int i);

#ifdef __cplusplus
}/* extern "C" */
#endif /* __cplusplus */

#endif /* HAVE_FFS */
#endif /* __CVC4__LIB__FFS_H */
