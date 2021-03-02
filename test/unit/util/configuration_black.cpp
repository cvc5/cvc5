/*********************                                                        */
/*! \file configuration_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Configuration.
 **
 ** Black box testing of CVC4::Configuration.
 **/

#include "base/configuration.h"
#include "test.h"

namespace CVC4 {
namespace test {

class TestUtilBlackConfiguration : public TestInternal
{
};

TEST_F(TestUtilBlackConfiguration, static_flags)
{
  const bool debug =
#ifdef CVC4_DEBUG
      true;
#else  /* CVC4_DEBUG */
      false;
#endif /* CVC4_DEBUG */

  const bool tracing =
#ifdef CVC4_TRACING
      true;
#else  /* CVC4_TRACING */
      false;
#endif /* CVC4_TRACING */

  const bool muzzled =
#ifdef CVC4_MUZZLE
      true;
#else  /* CVC4_MUZZLE */
      false;
#endif /* CVC4_MUZZLE */

  const bool assertions =
#ifdef CVC4_ASSERTIONS
      true;
#else  /* CVC4_ASSERTIONS */
      false;
#endif /* CVC4_ASSERTIONS */

  const bool coverage =
#ifdef CVC4_COVERAGE
      true;
#else  /* CVC4_COVERAGE */
      false;
#endif /* CVC4_COVERAGE */

  const bool profiling =
#ifdef CVC4_PROFILING
      true;
#else  /* CVC4_PROFILING */
      false;
#endif /* CVC4_PROFILING */

  ASSERT_EQ(Configuration::isDebugBuild(), debug);
  ASSERT_EQ(Configuration::isTracingBuild(), tracing);
  ASSERT_EQ(Configuration::isMuzzledBuild(), muzzled);
  ASSERT_EQ(Configuration::isAssertionBuild(), assertions);
  ASSERT_EQ(Configuration::isCoverageBuild(), coverage);
  ASSERT_EQ(Configuration::isProfilingBuild(), profiling);
}

TEST_F(TestUtilBlackConfiguration, package_name)
{
  ASSERT_EQ(Configuration::getPackageName(), "cvc4");
}

TEST_F(TestUtilBlackConfiguration, versions)
{
  // just test that the functions exist
  Configuration::getVersionString();
  Configuration::getVersionMajor();
  Configuration::getVersionMinor();
  Configuration::getVersionRelease();
}

TEST_F(TestUtilBlackConfiguration, about)
{
  // just test that the function exists
  Configuration::about();
}
}  // namespace test
}  // namespace CVC4
