/*********************                                                        */
/*! \file configuration.cpp
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): acsys, cconway
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of Configuration class, which provides compile-time
 ** configuration information about the CVC4 library
 **
 ** Implementation of Configuration class, which provides compile-time
 ** configuration information about the CVC4 library.
 **/

#include <string>
#include <sstream>

#include "util/configuration.h"
#include "util/configuration_private.h"
#include "cvc4autoconfig.h"

#ifdef CVC4_DEBUG
#  include "util/Debug_tags.h"
#endif /* CVC4_DEBUG */

#ifdef CVC4_TRACING
#  include "util/Trace_tags.h"
#endif /* CVC4_TRACING */

using namespace std;

namespace CVC4 {

string Configuration::getName() {
  return PACKAGE_NAME;
}

bool Configuration::isDebugBuild() {
  return IS_DEBUG_BUILD;
}

bool Configuration::isStatisticsBuild() {
  return IS_STATISTICS_BUILD;
}

bool Configuration::isReplayBuild() {
  return IS_REPLAY_BUILD;
}

bool Configuration::isTracingBuild() {
  return IS_TRACING_BUILD;
}

bool Configuration::isDumpingBuild() {
  return IS_DUMPING_BUILD;
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

bool Configuration::isCompetitionBuild() {
  return IS_COMPETITION_BUILD;
}

string Configuration::getPackageName() {
  return PACKAGE_NAME;
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

std::string Configuration::about() {
  return CVC4_ABOUT_STRING;
}

bool Configuration::isBuiltWithGmp() {
  return IS_GMP_BUILD;
}

bool Configuration::isBuiltWithCln() {
  return IS_CLN_BUILD;
}

bool Configuration::isBuiltWithCudd() {
  return IS_CUDD_BUILD;
}

bool Configuration::isBuiltWithTlsSupport() {
  return USING_TLS;
}

unsigned Configuration::getNumDebugTags() {
#if CVC4_DEBUG
  /* -1 because a NULL pointer is inserted as the last value */
  return sizeof(Debug_tags) / sizeof(Debug_tags[0]) - 1;
#else /* CVC4_DEBUG */
  return 0;
#endif /* CVC4_DEBUG */
}

char const* const* Configuration::getDebugTags() {
#if CVC4_DEBUG
  return Debug_tags;
#else /* CVC4_DEBUG */
  static char const* no_tags[] = { NULL };
  return no_tags;
#endif /* CVC4_DEBUG */
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

bool Configuration::isSubversionBuild() {
  return IS_SUBVERSION_BUILD;
}

const char* Configuration::getSubversionBranchName() {
  return SUBVERSION_BRANCH_NAME;
}

unsigned Configuration::getSubversionRevision() {
  return SUBVERSION_REVISION;
}

bool Configuration::hasSubversionModifications() {
  return SUBVERSION_HAS_MODIFICATIONS;
}

string Configuration::getSubversionId() {
  if(! isSubversionBuild()) {
    return "";
  }

  stringstream ss;
  ss << "subversion " << getSubversionBranchName() << " r" << getSubversionRevision()
     << ( ::CVC4::Configuration::hasSubversionModifications() ? " (with modifications)" : "" );
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
