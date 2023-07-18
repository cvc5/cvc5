/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
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

#include <algorithm>
#include <sstream>
#include <string>

#include "base/Trace_tags.h"
#include "base/configuration_private.h"
#include "base/cvc5config.h"

using namespace std;

namespace cvc5::internal {

string Configuration::getName() { return CVC5_PACKAGE_NAME; }

bool Configuration::isDebugBuild() {
  return IS_DEBUG_BUILD;
}

bool Configuration::isTracingBuild() {
  return IS_TRACING_BUILD;
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
  return CVC5_STATIC_BUILD;
}

string Configuration::getPackageName() { return CVC5_PACKAGE_NAME; }

string Configuration::getVersionString() { return CVC5_FULL_VERSION; }

std::string Configuration::copyright() {
  std::stringstream ss;
  ss << "Copyright (c) 2009-2022 by the authors and their institutional\n"
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

  ss << "This version of cvc5 is linked against the following non-(L)GPL'ed\n"
     << "third party libraries.\n\n";

  ss << "  CaDiCaL - Simplified Satisfiability Solver\n"
     << "  See https://github.com/arminbiere/cadical for copyright "
     << "information.\n\n";

  if (Configuration::isBuiltWithCryptominisat()
      || Configuration::isBuiltWithKissat()
      || Configuration::isBuiltWithEditline())
  {
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
            "https://github.com/cvc5/cvc5/blob/main/INSTALL.md\n\n";
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
  ss << "This is cvc5 version " << getVersionString();
  if (Configuration::isGitBuild()) {
    ss << " [" << Configuration::getGitInfo() << "]";
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

bool Configuration::isBuiltWithCryptominisat() {
  return IS_CRYPTOMINISAT_BUILD;
}

bool Configuration::isBuiltWithKissat() { return IS_KISSAT_BUILD; }

bool Configuration::isBuiltWithEditline() { return IS_EDITLINE_BUILD; }

bool Configuration::isBuiltWithPoly()
{
  return IS_POLY_BUILD;
}
bool Configuration::isBuiltWithCoCoA() { return IS_COCOA_BUILD; }

const std::vector<std::string>& Configuration::getTraceTags()
{
  return Trace_tags;
}

bool Configuration::isTraceTag(const std::string& tag)
{
  return std::find(Trace_tags.begin(), Trace_tags.end(), tag)
         != Trace_tags.end();
}

bool Configuration::isGitBuild() {
  return GIT_BUILD;
}

std::string Configuration::getGitInfo() {
  return CVC5_GIT_INFO;
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

}  // namespace cvc5::internal
