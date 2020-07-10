/*********************                                                        */
/*! \file configuration.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Aina Niemetz, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of Configuration class, which provides compile-time
 ** configuration information about the CVC4 library
 **
 ** Implementation of Configuration class, which provides compile-time
 ** configuration information about the CVC4 library.
 **/
#include "base/configuration.h"

#include <stdlib.h>
#include <string.h>

#include <sstream>
#include <string>

#include "cvc4autoconfig.h"
#include "base/configuration_private.h"

#if defined(CVC4_DEBUG) && defined(CVC4_TRACING)
#  include "base/Debug_tags.h"
#endif /* CVC4_DEBUG && CVC4_TRACING */

#ifdef CVC4_TRACING
#  include "base/Trace_tags.h"
#endif /* CVC4_TRACING */

using namespace std;

namespace CVC4 {

string Configuration::getName() {
  return CVC4_PACKAGE_NAME;
}

bool Configuration::isDebugBuild() {
  return IS_DEBUG_BUILD;
}

bool Configuration::isStatisticsBuild() {
  return IS_STATISTICS_BUILD;
}

bool Configuration::isTracingBuild() {
  return IS_TRACING_BUILD;
}

bool Configuration::isDumpingBuild() {
  return IS_DUMPING_BUILD && !IS_MUZZLED_BUILD;
}

bool Configuration::isMuzzledBuild() {
  return IS_MUZZLED_BUILD;
}

bool Configuration::isAssertionBuild() {
  return IS_ASSERTIONS_BUILD;
}

bool Configuration::isProofBuild() {
  return IS_PROOFS_BUILD;
}

bool Configuration::isCoverageBuild() {
  return IS_COVERAGE_BUILD;
}

bool Configuration::isProfilingBuild() {
  return IS_PROFILING_BUILD;
}

bool Configuration::isAsanBuild() { return IS_ASAN_BUILD; }

bool Configuration::isUbsanBuild() { return IS_UBSAN_BUILD; }

bool Configuration::isTsanBuild() { return IS_TSAN_BUILD; }

bool Configuration::isCompetitionBuild() {
  return IS_COMPETITION_BUILD;
}

string Configuration::getPackageName() {
  return CVC4_PACKAGE_NAME;
}

string Configuration::getVersionString() {
  return CVC4_RELEASE_STRING;
}

unsigned Configuration::getVersionMajor() {
  return CVC4_MAJOR;
}

unsigned Configuration::getVersionMinor() {
  return CVC4_MINOR;
}

unsigned Configuration::getVersionRelease() {
  return CVC4_RELEASE;
}

std::string Configuration::getVersionExtra() {
  return CVC4_EXTRAVERSION;
}

std::string Configuration::copyright() {
  std::stringstream ss;
  ss << "Copyright (c) 2009-2020 by the authors and their institutional\n"
     << "affiliations listed at http://cvc4.cs.stanford.edu/authors\n\n";

  if (Configuration::licenseIsGpl()) {
    ss << "This build of CVC4 uses GPLed libraries, and is thus covered by\n"
       << "the GNU General Public License (GPL) version 3.  Versions of CVC4\n"
       << "are available that are covered by the (modified) BSD license. If\n"
       << "you want to license CVC4 under this license, please configure CVC4\n"
       << "with the \"--no-gpl\" option before building from sources.\n\n";
  } else {
    ss << "CVC4 is open-source and is covered by the BSD license (modified)."
       << "\n\n";
  }

  ss << "THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.\n"
     << "USE AT YOUR OWN RISK.\n\n";

  ss << "CVC4 incorporates code from ANTLR3 (http://www.antlr.org).\n"
     << "See licenses/antlr3-LICENSE for copyright and licensing information."
     << "\n\n";

  if (Configuration::isBuiltWithAbc() || Configuration::isBuiltWithLfsc()
      || Configuration::isBuiltWithCadical()
      || Configuration::isBuiltWithCryptominisat()
      || Configuration::isBuiltWithKissat()
      || Configuration::isBuiltWithSymFPU())
  {
    ss << "This version of CVC4 is linked against the following non-(L)GPL'ed\n"
       << "third party libraries.\n\n";
    if (Configuration::isBuiltWithAbc()) {
      ss << "  ABC - A System for Sequential Synthesis and Verification\n"
         << "  See http://bitbucket.org/alanmi/abc for copyright and\n"
         << "  licensing information.\n\n";
    }
    if (Configuration::isBuiltWithLfsc()) {
      ss << "  LFSC Proof Checker\n"
         << "  See http://github.com/CVC4/LFSC for copyright and\n"
         << "  licensing information.\n\n";
    }
    if (Configuration::isBuiltWithCadical())
    {
      ss << "  CaDiCaL - Simplified Satisfiability Solver\n"
         << "  See https://github.com/arminbiere/cadical for copyright "
         << "information.\n\n";
    }
    if (Configuration::isBuiltWithCryptominisat())
    {
      ss << "  CryptoMiniSat - An Advanced SAT Solver\n"
         << "  See https://github.com/msoos/cryptominisat for copyright "
         << "information.\n\n";
    }
    if (Configuration::isBuiltWithKissat())
    {
      ss << "  Kissat - Simplified Satisfiability Solver\n"
         << "  See https://fmv.jku.at/kissat for copyright "
         << "information.\n\n";
    }
    if (Configuration::isBuiltWithSymFPU())
    {
      ss << "  SymFPU - The Symbolic Floating Point Unit\n"
         << "  See https://github.com/martin-cs/symfpu/tree/CVC4 for copyright "
         << "information.\n\n";
    }
  }

  if (Configuration::isBuiltWithGmp() || Configuration::isBuiltWithPoly())
  {
    ss << "This version of CVC4 is linked against the following third party\n"
       << "libraries covered by the LGPLv3 license.\n"
       << "See licenses/lgpl-3.0.txt for more information.\n\n";
    if (Configuration::isBuiltWithGmp()) {
      ss << "  GMP - Gnu Multi Precision Arithmetic Library\n"
         << "  See http://gmplib.org for copyright information.\n\n";
    }
    if (Configuration::isBuiltWithPoly()) {
      ss << "  LibPoly polynomial library\n"
         << "  See https://github.com/SRI-CSL/libpoly for copyright and\n"
         << "  licensing information.\n\n";
    }
  }

  if (Configuration::isBuiltWithCln()
      || Configuration::isBuiltWithGlpk ()
      || Configuration::isBuiltWithReadline()) {
    ss << "This version of CVC4 is linked against the following third party\n"
       << "libraries covered by the GPLv3 license.\n"
       << "See licenses/gpl-3.0.txt for more information.\n\n";
    if (Configuration::isBuiltWithCln()) {
      ss << "  CLN - Class Library for Numbers\n"
         << "  See http://www.ginac.de/CLN for copyright information.\n\n";
    }
    if (Configuration::isBuiltWithGlpk()) {
      ss << "  glpk-cut-log -  a modified version of GPLK, "
         << "the GNU Linear Programming Kit\n"
         << "  See http://github.com/timothy-king/glpk-cut-log for copyright"
         << "information\n\n";
    }
    if (Configuration::isBuiltWithReadline()) {
      ss << "  GNU Readline\n"
         << "  See http://cnswww.cns.cwru.edu/php/chet/readline/rltop.html\n"
         << "  for copyright information.\n\n";
    }
  }

  ss << "See the file COPYING (distributed with the source code, and with\n"
     << "all binaries) for the full CVC4 copyright, licensing, and (lack of)\n"
     << "warranty information.\n";
  return ss.str();
}

std::string Configuration::about() {
  std::stringstream ss;
  ss << "This is CVC4 version " << CVC4_RELEASE_STRING;
  if (Configuration::isGitBuild()) {
    ss << " [" << Configuration::getGitId() << "]";
  }
  ss << "\ncompiled with " << Configuration::getCompiler()
     << "\non " << Configuration::getCompiledDateTime() << "\n\n";
  ss << Configuration::copyright ();
  return ss.str();
}

bool Configuration::licenseIsGpl() {
  return IS_GPL_BUILD;
}

bool Configuration::isBuiltWithGmp() {
  return IS_GMP_BUILD;
}

bool Configuration::isBuiltWithCln() {
  return IS_CLN_BUILD;
}

bool Configuration::isBuiltWithGlpk() {
  return IS_GLPK_BUILD;
}

bool Configuration::isBuiltWithAbc() {
  return IS_ABC_BUILD;
}

bool Configuration::isBuiltWithCadical() { return IS_CADICAL_BUILD; }

bool Configuration::isBuiltWithCryptominisat() {
  return IS_CRYPTOMINISAT_BUILD;
}

bool Configuration::isBuiltWithKissat() { return IS_KISSAT_BUILD; }

bool Configuration::isBuiltWithDrat2Er() { return IS_DRAT2ER_BUILD; }

bool Configuration::isBuiltWithReadline() {
  return IS_READLINE_BUILD;
}

bool Configuration::isBuiltWithLfsc() {
  return IS_LFSC_BUILD;
}

bool Configuration::isBuiltWithPoly() {
  return IS_POLY_BUILD;
}

bool Configuration::isBuiltWithSymFPU() { return IS_SYMFPU_BUILD; }

unsigned Configuration::getNumDebugTags() {
#if defined(CVC4_DEBUG) && defined(CVC4_TRACING)
  /* -1 because a NULL pointer is inserted as the last value */
  return (sizeof(Debug_tags) / sizeof(Debug_tags[0])) - 1;
#else /* CVC4_DEBUG && CVC4_TRACING */
  return 0;
#endif /* CVC4_DEBUG && CVC4_TRACING */
}

char const* const* Configuration::getDebugTags() {
#if defined(CVC4_DEBUG) && defined(CVC4_TRACING)
  return Debug_tags;
#else /* CVC4_DEBUG && CVC4_TRACING */
  static char const* no_tags[] = { NULL };
  return no_tags;
#endif /* CVC4_DEBUG && CVC4_TRACING */
}

int strcmpptr(const char **s1, const char **s2){
  return strcmp(*s1,*s2);
}

bool Configuration::isDebugTag(char const *tag){
#if defined(CVC4_DEBUG) && defined(CVC4_TRACING)
  unsigned ntags = getNumDebugTags();
  char const* const* tags = getDebugTags();
  for (unsigned i = 0; i < ntags; ++ i) {
    if (strcmp(tag, tags[i]) == 0) {
      return true;
    }
  }
#endif /* CVC4_DEBUG && CVC4_TRACING */
  return false;
}

unsigned Configuration::getNumTraceTags() {
#if CVC4_TRACING
  /* -1 because a NULL pointer is inserted as the last value */
  return sizeof(Trace_tags) / sizeof(Trace_tags[0]) - 1;
#else /* CVC4_TRACING */
  return 0;
#endif /* CVC4_TRACING */
}

char const* const* Configuration::getTraceTags() {
#if CVC4_TRACING
  return Trace_tags;
#else /* CVC4_TRACING */
  static char const* no_tags[] = { NULL };
  return no_tags;
#endif /* CVC4_TRACING */
}

bool Configuration::isTraceTag(char const * tag){
#if CVC4_TRACING
  unsigned ntags = getNumTraceTags();
  char const* const* tags = getTraceTags();
  for (unsigned i = 0; i < ntags; ++ i) {
    if (strcmp(tag, tags[i]) == 0) {
      return true;
    }
  }
#endif /* CVC4_TRACING */
  return false;
}

bool Configuration::isGitBuild() {
  return IS_GIT_BUILD;
}

const char* Configuration::getGitBranchName() {
  return GIT_BRANCH_NAME;
}

const char* Configuration::getGitCommit() {
  return GIT_COMMIT;
}

bool Configuration::hasGitModifications() {
  return GIT_HAS_MODIFICATIONS;
}

std::string Configuration::getGitId() {
  if(! isGitBuild()) {
    return "";
  }

  const char* branchName = getGitBranchName();
  if(*branchName == '\0') {
    branchName = "-";
  }

  stringstream ss;
  ss << "git " << branchName << " " << string(getGitCommit()).substr(0, 8)
     << ( ::CVC4::Configuration::hasGitModifications() ? " (with modifications)" : "" );
  return ss.str();
}

std::string Configuration::getCompiler() {
  stringstream ss;
#ifdef __GNUC__
  ss << "GCC";
#else /* __GNUC__ */
  ss << "unknown compiler";
#endif /* __GNUC__ */
#ifdef __VERSION__
  ss << " version " << __VERSION__;
#else /* __VERSION__ */
  ss << ", unknown version";
#endif /* __VERSION__ */
  return ss.str();
}

std::string Configuration::getCompiledDateTime() {
  return __DATE__ " " __TIME__;
}

}/* CVC4 namespace */
