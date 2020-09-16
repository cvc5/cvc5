/*********************                                                        */
/*! \file configuration_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Configuration.
 **
 ** Black box testing of CVC4::Configuration.
 **/

#include <cxxtest/TestSuite.h>

#include "base/configuration.h"

using namespace CVC4;
using namespace std;

class ConfigurationBlack : public CxxTest::TestSuite {

public:

  void testStaticFlags() {
    const bool debug =
#ifdef CVC4_DEBUG
      true;
#else /* CVC4_DEBUG */
      false;
#endif /* CVC4_DEBUG */

    const bool tracing =
#ifdef CVC4_TRACING
      true;
#else /* CVC4_TRACING */
      false;
#endif /* CVC4_TRACING */

    const bool muzzled =
#ifdef CVC4_MUZZLE
      true;
#else /* CVC4_MUZZLE */
      false;
#endif /* CVC4_MUZZLE */

    const bool assertions =
#ifdef CVC4_ASSERTIONS
      true;
#else /* CVC4_ASSERTIONS */
      false;
#endif /* CVC4_ASSERTIONS */

    const bool coverage =
#ifdef CVC4_COVERAGE
      true;
#else /* CVC4_COVERAGE */
      false;
#endif /* CVC4_COVERAGE */

    const bool profiling =
#ifdef CVC4_PROFILING
      true;
#else /* CVC4_PROFILING */
      false;
#endif /* CVC4_PROFILING */

    TS_ASSERT( Configuration::isDebugBuild() == debug );
    TS_ASSERT( Configuration::isTracingBuild() == tracing );
    TS_ASSERT( Configuration::isMuzzledBuild() == muzzled );
    TS_ASSERT( Configuration::isAssertionBuild() == assertions );
    TS_ASSERT( Configuration::isCoverageBuild() == coverage );
    TS_ASSERT( Configuration::isProfilingBuild() == profiling );
  }

  void testPackageName() {
    TS_ASSERT( Configuration::getPackageName() == "cvc4" );
  }

  void testVersions() {
    // just test that the functions exist
    Configuration::getVersionString();
    Configuration::getVersionMajor();
    Configuration::getVersionMinor();
    Configuration::getVersionRelease();
  }

  void testAbout() {
    // just test that the function exists
    Configuration::about();
  }

};
