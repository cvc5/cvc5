/*********************                                                        */
/*! \file configuration_private.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: acsys
 ** Minor contributors (to current version): cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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

#include <string>
#include "util/configuration.h"

namespace CVC4 {

#ifdef CVC4_DEBUG
#  define IS_DEBUG_BUILD true
#else /* CVC4_DEBUG */
#  define IS_DEBUG_BUILD false
#endif /* CVC4_DEBUG */

#ifdef CVC4_STATISTICS_ON
#  define IS_STATISTICS_BUILD true
#else /* CVC4_STATISTICS_ON */
#  define IS_STATISTICS_BUILD false
#endif /* CVC4_STATISTICS_ON */

#ifdef CVC4_REPLAY
#  define IS_REPLAY_BUILD true
#else /* CVC4_REPLAY */
#  define IS_REPLAY_BUILD false
#endif /* CVC4_REPLAY */

#ifdef CVC4_TRACING
#  define IS_TRACING_BUILD true
#else /* CVC4_TRACING */
#  define IS_TRACING_BUILD false
#endif /* CVC4_TRACING */

#ifdef CVC4_DUMPING
#  define IS_DUMPING_BUILD true
#else /* CVC4_DUMPING */
#  define IS_DUMPING_BUILD false
#endif /* CVC4_DUMPING */

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

#ifdef CVC4_CUDD
#  define IS_CUDD_BUILD true
#else /* CVC4_CUDD */
#  define IS_CUDD_BUILD false
#endif /* CVC4_CUDD */

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

#define CVC4_ABOUT_STRING ( ::std::string("\
This is CVC4 version " CVC4_RELEASE_STRING ) + \
    ( ::CVC4::Configuration::isSubversionBuild() \
        ? ( ::std::string(" [") + ::CVC4::Configuration::getSubversionId() + "]" ) \
        : ::std::string("") \
    ) + "\n\
compiled with " + ::CVC4::Configuration::getCompiler() + "\n\n\
Copyright (C) 2009, 2010, 2011\n\
  The ACSys Group\n\
  Courant Institute of Mathematical Sciences\n\
  New York University\n\
  New York, NY  10012  USA\n\n" + \
    ( IS_CLN_BUILD ? "\
This CVC4 library uses CLN as its multi-precision arithmetic library.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n\
However, CLN, the Class Library for Numbers, is covered by the GPL.  Thus\n\
this CVC4 library cannot be used in proprietary applications.  Please\n\
consult the CVC4 documentation for instructions about building a version\n\
of CVC4 that links against GMP, and can be used in such applications.\n" : \
"This CVC4 library uses GMP as its multi-precision arithmetic library.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n\n\
THIS SOFTWARE PROVIDED AS-IS, WITHOUT ANY WARRANTIES. USE IT AT YOUR OWN RISK.\n" ) )

}/* CVC4 namespace */

#endif /* __CVC4__CONFIGURATION_PRIVATE_H */
