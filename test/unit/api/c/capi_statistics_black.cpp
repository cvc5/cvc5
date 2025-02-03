/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of solver functions of the C API.
 */

extern "C" {
#include <cvc5/c/cvc5.h>
}

#include <cmath>

#include "base/check.h"
#include "base/output.h"
#include "gtest/gtest.h"

namespace cvc5::internal::test {

class TestCApiBlackStatistics : public ::testing::Test
{
 protected:
  void SetUp() override
  {
    d_tm = cvc5_term_manager_new();
    d_solver = cvc5_new(d_tm);
    cvc5_check_sat(d_solver);
  }
  void TearDown() override
  {
    cvc5_delete(d_solver);
    cvc5_term_manager_delete(d_tm);
  }
  Cvc5TermManager* d_tm;
  Cvc5* d_solver;
};

TEST_F(TestCApiBlackStatistics, stat_is_internal)
{
  ASSERT_DEATH(cvc5_stat_is_internal(nullptr), "invalid statistic");
  Cvc5Stat stat = cvc5_stats_get(cvc5_get_statistics(d_solver),
                                 "theory::strings::checkRuns");
  ASSERT_TRUE(cvc5_stat_is_int(stat));
  ASSERT_TRUE(cvc5_stat_is_internal(stat));
}

TEST_F(TestCApiBlackStatistics, stat_is_default)
{
  ASSERT_DEATH(cvc5_stat_is_default(nullptr), "invalid statistic");
  Cvc5Stat stat = cvc5_stats_get(cvc5_get_statistics(d_solver),
                                 "theory::strings::checkRuns");
  ASSERT_TRUE(cvc5_stat_is_int(stat));
  ASSERT_FALSE(cvc5_stat_is_default(stat));
}

TEST_F(TestCApiBlackStatistics, stat_is_int)
{
  ASSERT_DEATH(cvc5_stat_is_int(nullptr), "invalid statistic");
  Cvc5Stat stat = cvc5_stats_get(cvc5_get_statistics(d_solver),
                                 "theory::strings::checkRuns");
  ASSERT_TRUE(cvc5_stat_is_int(stat));
}

TEST_F(TestCApiBlackStatistics, stat_get_int)
{
  ASSERT_DEATH(cvc5_stat_get_int(nullptr), "invalid statistic");
  Cvc5Stat stat = cvc5_stats_get(cvc5_get_statistics(d_solver),
                                 "theory::strings::checkRuns");
  ASSERT_TRUE(cvc5_stat_is_int(stat));
  (void)cvc5_stat_get_int(stat);
  stat = cvc5_stats_get(cvc5_get_statistics(d_solver), "global::totalTime");
  ASSERT_TRUE(cvc5_stat_is_string(stat));
  ASSERT_DEATH(cvc5_stat_get_int(stat), "expected Stat of type int64_t");
}

TEST_F(TestCApiBlackStatistics, stat_is_double)
{
  ASSERT_DEATH(cvc5_stat_is_double(nullptr), "invalid statistic");
  Cvc5Stat stat =
      cvc5_stats_get(cvc5_get_statistics(d_solver), "global::totalTime");
  ASSERT_FALSE(cvc5_stat_is_double(stat));
}

TEST_F(TestCApiBlackStatistics, stat_get_double)
{
  ASSERT_DEATH(cvc5_stat_get_double(nullptr), "invalid statistic");
  Cvc5Stat stat =
      cvc5_stats_get(cvc5_get_statistics(d_solver), "global::totalTime");
  ASSERT_FALSE(cvc5_stat_is_double(stat));
  ASSERT_DEATH(cvc5_stat_get_double(stat), "expected Stat of type double");
}

TEST_F(TestCApiBlackStatistics, stat_is_string)
{
  ASSERT_DEATH(cvc5_stat_is_string(nullptr), "invalid statistic");
  Cvc5Stat stat =
      cvc5_stats_get(cvc5_get_statistics(d_solver), "global::totalTime");
  ASSERT_TRUE(cvc5_stat_is_string(stat));
}

TEST_F(TestCApiBlackStatistics, stat_get_string)
{
  ASSERT_DEATH(cvc5_stat_get_string(nullptr), "invalid statistic");
  Cvc5Stat stat =
      cvc5_stats_get(cvc5_get_statistics(d_solver), "global::totalTime");
  ASSERT_TRUE(cvc5_stat_is_string(stat));
  (void)cvc5_stat_get_string(stat);
  stat = cvc5_stats_get(cvc5_get_statistics(d_solver),
                        "theory::strings::checkRuns");
  ASSERT_FALSE(cvc5_stat_is_string(stat));
  ASSERT_DEATH(cvc5_stat_get_string(stat), "expected Stat of type std::string");
}

TEST_F(TestCApiBlackStatistics, stat_is_histogram)
{
  ASSERT_DEATH(cvc5_stat_is_histogram(nullptr), "invalid statistic");
  Cvc5Stat stat = cvc5_stats_get(cvc5_get_statistics(d_solver),
                                 "theory::strings::reductions");
  ASSERT_TRUE(cvc5_stat_is_histogram(stat));
}

TEST_F(TestCApiBlackStatistics, stat_get_histogram)
{
  const char** keys;
  uint64_t* values;
  size_t size;
  Cvc5Stat stat = cvc5_stats_get(cvc5_get_statistics(d_solver),
                                 "theory::strings::reductions");
  ASSERT_TRUE(cvc5_stat_is_histogram(stat));
  cvc5_stat_get_histogram(stat, &keys, &values, &size);
  ASSERT_DEATH(cvc5_stat_get_histogram(nullptr, &keys, &values, &size),
               "invalid statistic");
  ASSERT_DEATH(cvc5_stat_get_histogram(stat, nullptr, &values, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_stat_get_histogram(stat, &keys, nullptr, &size),
               "unexpected NULL argument");
  ASSERT_DEATH(cvc5_stat_get_histogram(stat, &keys, &values, nullptr),
               "unexpected NULL argument");
  stat = cvc5_stats_get(cvc5_get_statistics(d_solver),
                        "theory::strings::checkRuns");
  ASSERT_FALSE(cvc5_stat_is_histogram(stat));
  ASSERT_DEATH(cvc5_stat_get_histogram(stat, &keys, &values, &size),
               "expected Stat of typ");
}

TEST_F(TestCApiBlackStatistics, stat_to_string)
{
  ASSERT_DEATH(cvc5_stat_to_string(nullptr), "invalid statistic");
  Cvc5Stat stat = cvc5_stats_get(cvc5_get_statistics(d_solver),
                                 "theory::strings::reductions");
  (void)cvc5_stat_to_string(stat);
}

TEST_F(TestCApiBlackStatistics, stats_iter_init)
{
  ASSERT_DEATH(cvc5_stats_iter_init(nullptr, false, false),
               "invalid statistics");
  Cvc5Statistics stats = cvc5_get_statistics(d_solver);
  cvc5_stats_iter_init(stats, true, true);
}

TEST_F(TestCApiBlackStatistics, stats_iter_has_next)
{
  ASSERT_DEATH(cvc5_stats_iter_has_next(nullptr), "invalid statistics");
  Cvc5Statistics stats = cvc5_get_statistics(d_solver);
  ASSERT_DEATH(cvc5_stats_iter_has_next(stats), "iterator not initialized");
  cvc5_stats_iter_init(stats, true, true);
  ASSERT_TRUE(cvc5_stats_iter_has_next(stats));
}

TEST_F(TestCApiBlackStatistics, stats_iter_next)
{
  ASSERT_DEATH(cvc5_stats_iter_next(nullptr, nullptr), "invalid statistics");
  Cvc5Statistics stats = cvc5_get_statistics(d_solver);
  cvc5_stats_iter_init(stats, true, true);
  ASSERT_TRUE(cvc5_stats_iter_has_next(stats));
  (void)cvc5_stats_iter_next(stats, nullptr);
}

TEST_F(TestCApiBlackStatistics, stats_get)
{
  Cvc5Statistics stats = cvc5_get_statistics(d_solver);
  ASSERT_DEATH(cvc5_stats_get(nullptr, "global::totalTime"),
               "invalid statistics");
  ASSERT_DEATH(cvc5_stats_get(stats, nullptr), "unexpected NULL argument");
  (void)cvc5_stats_get(stats, "global::totalTime");
}

TEST_F(TestCApiBlackStatistics, stats_to_string)
{
  ASSERT_DEATH(cvc5_stats_to_string(nullptr), "invalid statistics");
  Cvc5Statistics stats = cvc5_get_statistics(d_solver);
  (void)cvc5_stats_to_string(stats);
}

}  // namespace cvc5::internal::test
