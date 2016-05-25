/*********************                                                        */
/*! \file configuration.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Francois Bobot
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Interface to a public class that provides compile-time information
 ** about the CVC4 library.
 **
 ** Interface to a public class that provides compile-time information
 ** about the CVC4 library.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__CONFIGURATION_H
#define __CVC4__CONFIGURATION_H

#include <string>

namespace CVC4 {

/**
 * Represents the (static) configuration of CVC4.
 */
class CVC4_PUBLIC Configuration {
private:
  /** Private default ctor: Disallow construction of this class */
  Configuration();

  // these constants are filled in by the build system
  static const bool IS_SUBVERSION_BUILD;
  static const char* const SUBVERSION_BRANCH_NAME;
  static const unsigned SUBVERSION_REVISION;
  static const bool SUBVERSION_HAS_MODIFICATIONS;
  static const bool IS_GIT_BUILD;
  static const char* const GIT_BRANCH_NAME;
  static const char* const GIT_COMMIT;
  static const bool GIT_HAS_MODIFICATIONS;

public:

  static std::string getName();

  static bool isDebugBuild();

  static bool isStatisticsBuild();

  static bool isReplayBuild();

  static bool isTracingBuild();

  static bool isDumpingBuild();

  static bool isMuzzledBuild();

  static bool isAssertionBuild();

  static bool isProofBuild();

  static bool isCoverageBuild();

  static bool isProfilingBuild();

  static bool isCompetitionBuild();

  static std::string getPackageName();

  static std::string getVersionString();

  static unsigned getVersionMajor();

  static unsigned getVersionMinor();

  static unsigned getVersionRelease();

  static std::string getVersionExtra();

  static std::string about();

  static bool licenseIsGpl();

  static bool isBuiltWithGmp();

  static bool isBuiltWithCln();

  static bool isBuiltWithGlpk();

  static bool isBuiltWithAbc();

  static bool isBuiltWithCryptominisat();

  static bool isBuiltWithReadline();

  static bool isBuiltWithCudd();

  static bool isBuiltWithTlsSupport();

  /* Return the number of debug tags */
  static unsigned getNumDebugTags();
  /* Return a sorted array of the debug tags name */
  static char const* const* getDebugTags();
  /* Test if the given argument is a known debug tag name */
  static bool isDebugTag(char const *);

  /* Return the number of trace tags */
  static unsigned getNumTraceTags();
  /* Return a sorted array of the trace tags name */
  static char const* const* getTraceTags();
  /* Test if the given argument is a known trace tag name */
  static bool isTraceTag(char const *);

  static bool isGitBuild();
  static const char* getGitBranchName();
  static const char* getGitCommit();
  static bool hasGitModifications();
  static std::string getGitId();

  static bool isSubversionBuild();
  static const char* getSubversionBranchName();
  static unsigned getSubversionRevision();
  static bool hasSubversionModifications();
  static std::string getSubversionId();

  static std::string getCompiler();
  static std::string getCompiledDateTime();

};/* class Configuration */

}/* CVC4 namespace */

#endif /* __CVC4__CONFIGURATION_H */
