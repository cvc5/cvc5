/******************************************************************************
 * Top contributors (to current version):
 *   Morgan Deters, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Interface to a public class that provides compile-time information
 * about the cvc5 library.
 */

#include "cvc5_public.h"

#ifndef CVC5__CONFIGURATION_H
#define CVC5__CONFIGURATION_H

#include <string>

#include "cvc5_export.h"

namespace cvc5 {

/**
 * Represents the (static) configuration of cvc5.
 */
class CVC5_EXPORT Configuration
{
 private:
  /** Private default ctor: Disallow construction of this class */
  Configuration();

  // these constants are filled in by the build system
  static const bool IS_GIT_BUILD;
  static const char* const GIT_BRANCH_NAME;
  static const char* const GIT_COMMIT;
  static const bool GIT_HAS_MODIFICATIONS;

public:

  static std::string getName();

  static bool isDebugBuild();

  static constexpr bool isStatisticsBuild()
  {
#ifdef CVC5_STATISTICS_ON
    return true;
#else
    return false;
#endif
  }

  static bool isTracingBuild();

  static bool isDumpingBuild();

  static bool isMuzzledBuild();

  static bool isAssertionBuild();

  static bool isCoverageBuild();

  static bool isProfilingBuild();

  static bool isAsanBuild();

  static bool isUbsanBuild();

  static bool isTsanBuild();

  static bool isCompetitionBuild();

  static bool isStaticBuild();

  static std::string getPackageName();

  static std::string getVersionString();

  static unsigned getVersionMajor();

  static unsigned getVersionMinor();

  static unsigned getVersionRelease();

  static std::string getVersionExtra();

  static std::string copyright();

  static std::string about();

  static bool licenseIsGpl();

  static bool isBuiltWithGmp();

  static bool isBuiltWithCln();

  static bool isBuiltWithGlpk();

  static bool isBuiltWithAbc();

  static bool isBuiltWithCadical();

  static bool isBuiltWithCryptominisat();

  static bool isBuiltWithKissat();

  static bool isBuiltWithEditline();

  static bool isBuiltWithPoly();

  static bool isBuiltWithSymFPU();

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

  static std::string getCompiler();
  static std::string getCompiledDateTime();

}; /* class Configuration */

}  // namespace cvc5

#endif /* CVC5__CONFIGURATION_H */
