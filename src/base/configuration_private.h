/*********************                                                        */
/*! \file configuration_private.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Christopher L. Conway, ACSYS
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Provides compile-time configuration information about the
 ** CVC4 library.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONFIGURATION_PRIVATE_H
#define __CVC4__CONFIGURATION_PRIVATE_H

#include <string>

#include "base/configuration.h"

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

#if CVC4_USE_ABC
#  define IS_ABC_BUILD true
#else /* CVC4_USE_ABC */
#  define IS_ABC_BUILD false
#endif /* CVC4_USE_ABC */

#if CVC4_USE_CRYPTOMINISAT
#  define IS_CRYPTOMINISAT_BUILD true
#else /* CVC4_USE_CRYPTOMINISAT */
#  define IS_CRYPTOMINISAT_BUILD false
#endif /* CVC4_USE_CRYPTOMINISAT */

#if CVC4_USE_LFSC
#define IS_LFSC_BUILD true
#else /* CVC4_USE_LFSC */
#define IS_LFSC_BUILD false
#endif /* CVC4_USE_LFSC */

#ifdef HAVE_LIBREADLINE
#  define IS_READLINE_BUILD true
#else /* HAVE_LIBREADLINE */
#  define IS_READLINE_BUILD false
#endif /* HAVE_LIBREADLINE */

#if CVC4_GPL_DEPS
#  define IS_GPL_BUILD true
#else /* CVC4_GPL_DEPS */
#  define IS_GPL_BUILD false
#endif /* CVC4_GPL_DEPS */

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
Copyright (c) 2009-2017\n\
by the authors and their institutional affiliations listed at \n\
http://cvc4.cs.stanford.edu/authors\n\n" + \
    ( IS_GPL_BUILD ? "\
This build of CVC4 uses GPLed libraries, and is thus covered by the GNU\n\
General Public License (GPL) version 3.  Versions of CVC4 are available\n\
that are covered by the (modified) BSD license.  If you want to license\n\
CVC4 under this license, please configure CVC4 with the \"--bsd\" option\n\
before building from sources.\n\
" : \
"This CVC4 library uses GMP as its multi-precision arithmetic library.\n\n\
CVC4 is open-source and is covered by the BSD license (modified).\n\n\
" ) + "\
THIS SOFTWARE PROVIDED AS-IS, WITHOUT ANY WARRANTIES. USE AT YOUR OWN RISK.\n\n\
See the file COPYING (distributed with the source code, and with all binaries)\n\
for the full CVC4 copyright, licensing, and (lack of) warranty information.\n" )

}/* CVC4 namespace */

#endif /* __CVC4__CONFIGURATION_PRIVATE_H */
