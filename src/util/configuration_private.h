/*********************                                                        */
/*! \file configuration_private.h
 ** \verbatim
 ** Original author: Christopher L. Conway
 ** Major contributors: ACSYS, Morgan Deters
 ** Minor contributors (to current version): Liana Hadarean, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
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

#ifdef CVC4_PROOF
#  define IS_PROOFS_BUILD true
#else  /* CVC4_PROOF */
#  define IS_PROOFS_BUILD false
#endif /* CVC4_PROOF */

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

#if CVC4_USE_GLPK
#  define IS_GLPK_BUILD true
#else /* CVC4_USE_GLPK */
#  define IS_GLPK_BUILD false
#endif /* CVC4_USE_GLPK */

#ifdef TLS
#  define USING_TLS true
#else /* TLS */
#  define USING_TLS false
#endif /* TLS */

#define CVC4_ABOUT_STRING ( ::std::string("\
This is CVC4 version " CVC4_RELEASE_STRING ) + \
    ( ::CVC4::Configuration::isGitBuild() \
        ? ( ::std::string(" [") + ::CVC4::Configuration::getGitId() + "]" ) \
        : \
    ( ::CVC4::Configuration::isSubversionBuild() \
        ? ( ::std::string(" [") + ::CVC4::Configuration::getSubversionId() + "]" ) \
        : ::std::string("") \
    )) + "\n\
compiled with " + ::CVC4::Configuration::getCompiler() + "\n\
on " + ::CVC4::Configuration::getCompiledDateTime() + "\n\n\
Copyright (C) 2009, 2010, 2011, 2012, 2013\n\
  New York University and The University of Iowa\n\n" + \
    ( IS_CLN_BUILD ? "\
This CVC4 library uses CLN as its multi-precision arithmetic library.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n\
However, CLN, the Class Library for Numbers, is covered by the GPLv3,\n\
and so this \"combined\" work, CVC4+CLN, is covered by the GPLv3 as well.\n\
Please consult the CVC4 documentation for instructions about building\n\
without CLN if you want to license CVC4 under the (modified) BSD license.\n\n\
" : ( IS_GLPK_BUILD ? "\
This CVC4 library uses GLPK in its arithmetic solver.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n\
However, GLPK, the GNU Linear Programming Kit, is covered by the GPLv3,\n\
and so this \"combined\" work, CVC4+GLPK, is covered by the GPLv3 as well.\n\
Please consult the CVC4 documentation for instructions about building\n\
without GLPK if you want to license CVC4 under the (modified) BSD license.\n\n\
" : \
"This CVC4 library uses GMP as its multi-precision arithmetic library.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n\n\
" ) ) + "\
THIS SOFTWARE PROVIDED AS-IS, WITHOUT ANY WARRANTIES. USE AT YOUR OWN RISK.\n\n\
See the file COPYING (distributed with the source code, and with all binaries)\n\
for the full CVC4 copyright, licensing, and (lack of) warranty information.\n" )

}/* CVC4 namespace */

#endif /* __CVC4__CONFIGURATION_PRIVATE_H */
