/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5::Configuration.
 */

#include "base/configuration.h"
#include "test.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackConfiguration : public TestInternal
{
};

TEST_F(TestUtilBlackConfiguration, static_flags)
{
  const bool debug =
#ifdef CVC5_DEBUG
      true;
#else  /* CVC5_DEBUG */
      false;
#endif /* CVC5_DEBUG */

  const bool tracing =
#ifdef CVC5_TRACING
      true;
#else  /* CVC5_TRACING */
      false;
#endif /* CVC5_TRACING */

  const bool muzzled =
#ifdef CVC5_MUZZLE
      true;
#else  /* CVC5_MUZZLE */
      false;
#endif /* CVC5_MUZZLE */

  const bool assertions =
#ifdef CVC5_ASSERTIONS
      true;
#else  /* CVC5_ASSERTIONS */
      false;
#endif /* CVC5_ASSERTIONS */

  const bool coverage =
#ifdef CVC5_COVERAGE
      true;
#else  /* CVC5_COVERAGE */
      false;
#endif /* CVC5_COVERAGE */

  const bool profiling =
#ifdef CVC5_PROFILING
      true;
#else  /* CVC5_PROFILING */
      false;
#endif /* CVC5_PROFILING */

  ASSERT_EQ(Configuration::isDebugBuild(), debug);
  ASSERT_EQ(Configuration::isTracingBuild(), tracing);
  ASSERT_EQ(Configuration::isMuzzledBuild(), muzzled);
  ASSERT_EQ(Configuration::isAssertionBuild(), assertions);
  ASSERT_EQ(Configuration::isCoverageBuild(), coverage);
  ASSERT_EQ(Configuration::isProfilingBuild(), profiling);
}

TEST_F(TestUtilBlackConfiguration, package_name)
{
  ASSERT_EQ(Configuration::getPackageName(), "cvc5");
}

TEST_F(TestUtilBlackConfiguration, versions)
{
  // just test that the functions exist
  Configuration::getVersionString();
}

TEST_F(TestUtilBlackConfiguration, about)
{
  // just test that the function exists
  Configuration::about();
}
}  // namespace test
}  // namespace cvc5::internal
