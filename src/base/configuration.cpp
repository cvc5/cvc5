/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Aina Niemetz, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Configuration class, which provides compile-time
 * configuration information about the cvc5 library.
 */
#include "base/configuration.h"

#include <stdlib.h>
#include <string.h>

#include <sstream>
#include <string>

#include "base/configuration_private.h"
#include "base/cvc5config.h"

#if defined(CVC5_DEBUG) && defined(CVC5_TRACING)
#  include "base/Debug_tags.h"
#endif /* CVC5_DEBUG && CVC5_TRACING */

#ifdef CVC5_TRACING
#  include "base/Trace_tags.h"
#endif /* CVC5_TRACING */

using namespace std;

namespace cvc5 {

string Configuration::getName() { return CVC5_PACKAGE_NAME; }

bool Configuration::isDebugBuild() {
  return IS_DEBUG_BUILD;
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

bool Configuration::isStaticBuild()
{
#if defined(CVC5_STATIC_BUILD)
  return true;
#else
  return false;
#endif
}

string Configuration::getPackageName() { return CVC5_PACKAGE_NAME; }

string Configuration::getVersionString() { return CVC5_RELEASE_STRING; }

unsigned Configuration::getVersionMajor() { return CVC5_MAJOR; }

unsigned Configuration::getVersionMinor() { return CVC5_MINOR; }

unsigned Configuration::getVersionRelease() { return CVC5_RELEASE; }

std::string Configuration::getVersionExtra() { return CVC5_EXTRAVERSION; }

std::string Configuration::copyright() {
  std::stringstream ss;
  ss << "Copyright (c) 2009-2021 by the authors and their institutional\n"
     << "affiliations listed at https://cvc5.github.io/people.html\n\n";

  if (Configuration::licenseIsGpl()) {
    ss << "This build of cvc5 uses GPLed libraries, and is thus covered by\n"
       << "the GNU General Public License (GPL) version 3.  Versions of cvc5\n"
       << "are available that are covered by the (modified) BSD license. If\n"
       << "you want to license cvc5 under this license, please configure cvc5\n"
       << "with the \"--no-gpl\" option before building from sources.\n\n";
  } else {
    ss << "cvc5 is open-source and is covered by the BSD license (modified)."
       << "\n\n";
  }

  ss << "THIS SOFTWARE IS PROVIDED AS-IS, WITHOUT ANY WARRANTIES.\n"
     << "USE AT YOUR OWN RISK.\n\n";

  ss << "cvc5 incorporates code from ANTLR3 (http://www.antlr.org).\n"
     << "See licenses/antlr3-LICENSE for copyright and licensing information."
     << "\n\n";

  ss << "This version of cvc5 is linked against the following non-(L)GPL'ed\n"
     << "third party libraries.\n\n";

  ss << "  CaDiCaL - Simplified Satisfiability Solver\n"
     << "  See https://github.com/arminbiere/cadical for copyright "
     << "information.\n\n";

  if (Configuration::isBuiltWithAbc()
      || Configuration::isBuiltWithCryptominisat()
      || Configuration::isBuiltWithKissat()
      || Configuration::isBuiltWithEditline())
  {
    if (Configuration::isBuiltWithAbc()) {
      ss << "  ABC - A System for Sequential Synthesis and Verification\n"
         << "  See http://bitbucket.org/alanmi/abc for copyright and\n"
         << "  licensing information.\n\n";
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
    if (Configuration::isBuiltWithEditline())
    {
      ss << "  Editline Library\n"
         << "  See https://thrysoee.dk/editline\n"
         << "  for copyright information.\n\n";
    }
  }

  ss << "  SymFPU - The Symbolic Floating Point Unit\n"
     << "  See https://github.com/martin-cs/symfpu/tree/cvc5 for copyright "
     << "information.\n\n";

  if (Configuration::isBuiltWithGmp() || Configuration::isBuiltWithPoly())
  {
    ss << "This version of cvc5 is linked against the following third party\n"
       << "libraries covered by the LGPLv3 license.\n"
       << "See licenses/lgpl-3.0.txt for more information.\n\n";
    if (Configuration::isBuiltWithGmp()) {
      ss << "  GMP - Gnu Multi Precision Arithmetic Library\n"
         << "  See http://gmplib.org for copyright information.\n\n";
    }
    if (Configuration::isBuiltWithPoly())
    {
      ss << "  LibPoly polynomial library\n"
         << "  See https://github.com/SRI-CSL/libpoly for copyright and\n"
         << "  licensing information.\n\n";
    }
    if (Configuration::isStaticBuild())
    {
      ss << "cvc5 is statically linked against these libraries. To recompile\n"
            "this version of cvc5 with different versions of these libraries\n"
            "follow the instructions on "
            "https://github.com/cvc5/cvc5/blob/master/INSTALL.md\n\n";
    }
  }

  if (Configuration::isBuiltWithCln()
      || Configuration::isBuiltWithGlpk ()) {
    ss << "This version of cvc5 is linked against the following third party\n"
       << "libraries covered by the GPLv3 license.\n"
       << "See licenses/gpl-3.0.txt for more information.\n\n";
    if (Configuration::isBuiltWithCln()) {
      ss << "  CLN - Class Library for Numbers\n"
         << "  See http://www.ginac.de/CLN for copyright information.\n\n";
    }
    if (Configuration::isBuiltWithGlpk()) {
      ss << "  glpk-cut-log - a modified version of GPLK, "
         << "the GNU Linear Programming Kit\n"
         << "  See http://github.com/timothy-king/glpk-cut-log for copyright"
         << " information\n\n";
    }
  }

  ss << "See the file COPYING (distributed with the source code, and with\n"
     << "all binaries) for the full cvc5 copyright, licensing, and (lack of)\n"
     << "warranty information.\n";
  return ss.str();
}

std::string Configuration::about() {
  std::stringstream ss;
  ss << "This is cvc5 version " << CVC5_RELEASE_STRING;
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

bool Configuration::isBuiltWithCryptominisat() {
  return IS_CRYPTOMINISAT_BUILD;
}

bool Configuration::isBuiltWithKissat() { return IS_KISSAT_BUILD; }

bool Configuration::isBuiltWithEditline() { return IS_EDITLINE_BUILD; }

bool Configuration::isBuiltWithPoly()
{
  return IS_POLY_BUILD;
}

unsigned Configuration::getNumDebugTags() {
#if defined(CVC5_DEBUG) && defined(CVC5_TRACING)
  /* -1 because a NULL pointer is inserted as the last value */
  return (sizeof(Debug_tags) / sizeof(Debug_tags[0])) - 1;
#else  /* CVC5_DEBUG && CVC5_TRACING */
  return 0;
#endif /* CVC5_DEBUG && CVC5_TRACING */
}

char const* const* Configuration::getDebugTags() {
#if defined(CVC5_DEBUG) && defined(CVC5_TRACING)
  return Debug_tags;
#else  /* CVC5_DEBUG && CVC5_TRACING */
  static char const* no_tags[] = { NULL };
  return no_tags;
#endif /* CVC5_DEBUG && CVC5_TRACING */
}

int strcmpptr(const char **s1, const char **s2){
  return strcmp(*s1,*s2);
}

bool Configuration::isDebugTag(char const *tag){
#if defined(CVC5_DEBUG) && defined(CVC5_TRACING)
  unsigned ntags = getNumDebugTags();
  char const* const* tags = getDebugTags();
  for (unsigned i = 0; i < ntags; ++ i) {
    if (strcmp(tag, tags[i]) == 0) {
      return true;
    }
  }
#endif /* CVC5_DEBUG && CVC5_TRACING */
  return false;
}

unsigned Configuration::getNumTraceTags() {
#if CVC5_TRACING
  /* -1 because a NULL pointer is inserted as the last value */
  return sizeof(Trace_tags) / sizeof(Trace_tags[0]) - 1;
#else  /* CVC5_TRACING */
  return 0;
#endif /* CVC5_TRACING */
}

char const* const* Configuration::getTraceTags() {
#if CVC5_TRACING
  return Trace_tags;
#else  /* CVC5_TRACING */
  static char const* no_tags[] = { NULL };
  return no_tags;
#endif /* CVC5_TRACING */
}

bool Configuration::isTraceTag(char const * tag){
#if CVC5_TRACING
  unsigned ntags = getNumTraceTags();
  char const* const* tags = getTraceTags();
  for (unsigned i = 0; i < ntags; ++ i) {
    if (strcmp(tag, tags[i]) == 0) {
      return true;
    }
  }
#endif /* CVC5_TRACING */
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
     << (::cvc5::Configuration::hasGitModifications() ? " (with modifications)"
                                                      : "");
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

}  // namespace cvc5
