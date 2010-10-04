/*********************                                                        */
/*! \file configuration_private.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: cconway, acsys
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Provides compile-time configuration information about the
 ** CVC4 library.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONFIGURATION_PRIVATE_H
#define __CVC4__CONFIGURATION_PRIVATE_H

using namespace std;

namespace CVC4 {

#ifdef CVC4_DEBUG
#  define IS_DEBUG_BUILD true
#else /* CVC4_DEBUG */
#  define IS_DEBUG_BUILD false
#endif /* CVC4_DEBUG */

#ifdef CVC4_TRACING
#  define IS_TRACING_BUILD true
#else /* CVC4_TRACING */
#  define IS_TRACING_BUILD false
#endif /* CVC4_TRACING */

#ifdef CVC4_MUZZLE
#  define IS_MUZZLED_BUILD true
#else /* CVC4_MUZZLE */
#  define IS_MUZZLED_BUILD false
#endif /* CVC4_MUZZLE */

#ifdef CVC4_ASSERTIONS
#  define IS_ASSERTIONS_BUILD true
#else /* CVC4_ASSERTIONS */
#  define IS_ASSERTIONS_BUILD false
#endif /* CVC4_ASSERTIONS */

#ifdef CVC4_COVERAGE
#  define IS_COVERAGE_BUILD true
#else /* CVC4_COVERAGE */
#  define IS_COVERAGE_BUILD false
#endif /* CVC4_COVERAGE */

#ifdef CVC4_PROFILING
#  define IS_PROFILING_BUILD true
#else /* CVC4_PROFILING */
#  define IS_PROFILING_BUILD false
#endif /* CVC4_PROFILING */

#ifdef CVC4_COMPETITION_MODE
#  define IS_COMPETITION_BUILD true
#else /* CVC4_COMPETITION_MODE */
#  define IS_COMPETITION_BUILD false
#endif /* CVC4_COMPETITION_MODE */

#ifdef CVC4_GMP_IMP
#  define IS_GMP_BUILD true
#else /* CVC4_GMP_IMP */
#  define IS_GMP_BUILD false
#endif /* CVC4_GMP_IMP */

#ifdef CVC4_CLN_IMP
#  define IS_CLN_BUILD true
#else /* CVC4_CLN_IMP */
#  define IS_CLN_BUILD false
#endif /* CVC4_CLN_IMP */

#ifdef TLS
#  define USING_TLS true
#else /* TLS */
#  define USING_TLS false
#endif /* TLS */

#define CVC4_ABOUT_STRING string("\
This is a pre-release of CVC4.\n\
Copyright (C) 2009, 2010\n\
  The ACSys Group\n\
  Courant Institute of Mathematical Sciences\n\
  New York University\n\
  New York, NY  10012  USA\n\n") + \
    (IS_CLN_BUILD ? "\
This CVC4 library uses CLN as its multi-precision arithmetic library.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n\
However, CLN, the Class Library for Numbers, is covered by the GPL.  Thus\n\
this CVC4 library cannot be used in proprietary applications.  Please\n\
consult the CVC4 documentation for instructions about building a version\n\
of CVC4 that links against GMP, and can be used in such applications.\n" : \
"This CVC4 library uses GMP as its multi-precision arithmetic library.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n")

}/* CVC4 namespace */

#endif /* __CVC4__CONFIGURATION_PRIVATE_H */
