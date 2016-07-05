/*********************                                                        */
/*! \file configuration.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Francois Bobot, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
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

bool Configuration::isBuiltWithReadline() {
  return IS_READLINE_BUILD;
}

bool Configuration::isBuiltWithCudd() {
  return false;
}

bool Configuration::isBuiltWithTlsSupport() {
  return USING_TLS;
}

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

std::string Configuration::getSubversionId() {
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
