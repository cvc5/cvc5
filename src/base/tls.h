/*********************                                                        */
/*! \file tls.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Definiton of CVC4_THREAD_LOCAL
 **
 ** This header defines CVC4_THREAD_LOCAL, which should be used instead of
 ** thread_local because it is not supported by all build types (e.g. Swig).
 **/

#include "cvc4_public.h"

#ifndef __CVC4__BASE__TLS_H
#define __CVC4__BASE__TLS_H

#if SWIG && (!defined(SWIG_VERSION) || SWIG_VERSION < 0x030000)
// SWIG versions older than 3.0 do not support thread_local, so just redefine
// CVC4_THREAD_LOCAL to be empty for those versions.
#define CVC4_THREAD_LOCAL
#else
#define CVC4_THREAD_LOCAL thread_local
#endif

#endif /* __CVC4__BASE__TLS_H */
