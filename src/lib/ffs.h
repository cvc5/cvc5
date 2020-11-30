/*********************                                                        */
/*! \file ffs.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Replacement for ffs() for systems without it (like Win32)
 **
 ** Replacement for ffs() for systems without it (like Win32).
 **/

#include "cvc4_private.h"

#ifndef CVC4__LIB__FFS_H
#define CVC4__LIB__FFS_H

//We include this for HAVE_FFS
#include "cvc4autoconfig.h"

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
#endif /* CVC4__LIB__FFS_H */
