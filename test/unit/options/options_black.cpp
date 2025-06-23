/******************************************************************************
 * Top contributors (to current version):
 *   Gereon Kremer, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the Solver class of the  C++ API.
 */

#include <cvc5/cvc5_types.h>

#include <algorithm>
#include <limits>

#include "options/option_exception.h"
#include "options/options_public.h"
#include "test_api.h"

namespace cvc5::internal {

namespace test {

template <class... Ts>
struct overloaded : Ts...
{
  using Ts::operator()...;
};
template <class... Ts>
overloaded(Ts...) -> overloaded<Ts...>;

class TestBlackOptions : public TestApi
{
 public:
  /**
   * Tests setting options for option "name", including error values.
   */
  void testSetOption(const std::string& name)
  {
    auto info = d_solver->getOptionInfo(name);

    try
    {
      std::visit(
          overloaded{
              [this, &name](const OptionInfo::VoidInfo& v) {
                d_solver->setOption(name, "");
              },
              [this, &name](const OptionInfo::ValueInfo<bool>& v) {
                d_solver->setOption(name, "false");
                d_solver->setOption(name, "true");
              },
              [this, &name](const OptionInfo::ValueInfo<std::string>& v) {
                d_solver->setOption(name, "foo");
              },
              [this, &name](const OptionInfo::NumberInfo<int64_t>& v) {
                std::pair<int64_t, int64_t> range{
                    std::numeric_limits<int64_t>::min(),
                    std::numeric_limits<int64_t>::max()};
                if (v.minimum)
                {
                  EXPECT_THROW(
                      d_solver->setOption(name, std::to_string(*v.minimum - 1)),
                      CVC5ApiOptionException);
                  EXPECT_NO_THROW(
                      d_solver->setOption(name, std::to_string(*v.minimum)));
                  range.first = *v.minimum;
                }
                if (v.maximum)
                {
                  EXPECT_THROW(
                      d_solver->setOption(name, std::to_string(*v.maximum + 1)),
                      CVC5ApiOptionException);
                  EXPECT_NO_THROW(
                      d_solver->setOption(name, std::to_string(*v.maximum)));
                  range.second = *v.maximum;
                }
                EXPECT_NO_THROW(d_solver->setOption(
                    name, std::to_string((range.first + range.second) / 2)));
                EXPECT_THROW(d_solver->setOption(name, "0123abc"),
                             CVC5ApiOptionException);
              },
              [this, &name](const OptionInfo::NumberInfo<uint64_t>& v) {
                std::pair<uint64_t, uint64_t> range{
                    std::numeric_limits<uint64_t>::min(),
                    std::numeric_limits<uint64_t>::max()};
                EXPECT_THROW(d_solver->setOption(name, "-1"),
                             CVC5ApiOptionException);
                if (v.minimum)
                {
                  EXPECT_THROW(
                      d_solver->setOption(name, std::to_string(*v.minimum - 1)),
                      CVC5ApiOptionException);
                  EXPECT_NO_THROW(
                      d_solver->setOption(name, std::to_string(*v.minimum)));
                  range.first = *v.minimum;
                }
                if (v.maximum)
                {
                  EXPECT_THROW(
                      d_solver->setOption(name, std::to_string(*v.maximum + 1)),
                      CVC5ApiOptionException);
                  EXPECT_NO_THROW(
                      d_solver->setOption(name, std::to_string(*v.maximum)));
                  range.second = *v.maximum;
                }
                EXPECT_NO_THROW(d_solver->setOption(
                    name, std::to_string((range.first + range.second) / 2)));
                EXPECT_THROW(d_solver->setOption(name, "0123abc"),
                             CVC5ApiOptionException);
              },
              [this, &name](const OptionInfo::NumberInfo<double>& v) {
                std::pair<double, double> range{
                    std::numeric_limits<double>::min(),
                    std::numeric_limits<double>::max()};
                if (v.minimum)
                {
                  EXPECT_THROW(
                      d_solver->setOption(name, std::to_string(*v.minimum - 1)),
                      CVC5ApiOptionException);
                  EXPECT_NO_THROW(
                      d_solver->setOption(name, std::to_string(*v.minimum)));
                  range.first = *v.minimum;
                }
                if (v.maximum)
                {
                  EXPECT_THROW(
                      d_solver->setOption(name, std::to_string(*v.maximum + 1)),
                      CVC5ApiOptionException);
                  EXPECT_NO_THROW(
                      d_solver->setOption(name, std::to_string(*v.maximum)));
                  range.second = *v.maximum;
                }
                EXPECT_NO_THROW(d_solver->setOption(
                    name, std::to_string((range.first + range.second) / 2)));
              },
              [this, &name](const OptionInfo::ModeInfo& v) {
                EXPECT_THROW(d_solver->setOption(name, "foobarbaz"),
                             CVC5ApiOptionException);
                for (const auto& m : v.modes)
                {
                  d_solver->setOption(name, m);
                  EXPECT_EQ(d_solver->getOption(name), m);
                }
                EXPECT_DEATH(d_solver->setOption(name, "help"), "");
              },
          },
          info.valueInfo);
    }
    catch (const CVC5ApiOptionException&)
    {
    }
  }
  /**
   * Sets a single valid option for option "name".
   */
  void testSetOptionOnce(const std::string& name)
  {
    auto info = d_solver->getOptionInfo(name);

    try
    {
      std::visit(
          overloaded{
              [this, &name](const OptionInfo::VoidInfo& v) {
                d_solver->setOption(name, "");
              },
              [this, &name](const OptionInfo::ValueInfo<bool>& v) {
                d_solver->setOption(name, "false");
              },
              [this, &name](const OptionInfo::ValueInfo<std::string>& v) {
                d_solver->setOption(name, "foo");
              },
              [this, &name](const OptionInfo::NumberInfo<int64_t>& v) {
                std::pair<int64_t, int64_t> range{
                    std::numeric_limits<int64_t>::min(),
                    std::numeric_limits<int64_t>::max()};
                d_solver->setOption(
                    name, std::to_string((range.first + range.second) / 2));
              },
              [this, &name](const OptionInfo::NumberInfo<uint64_t>& v) {
                std::pair<uint64_t, uint64_t> range{
                    std::numeric_limits<uint64_t>::min(),
                    std::numeric_limits<uint64_t>::max()};
                d_solver->setOption(
                    name, std::to_string((range.first + range.second) / 2));
              },
              [this, &name](const OptionInfo::NumberInfo<double>& v) {
                std::pair<double, double> range{
                    std::numeric_limits<double>::min(),
                    std::numeric_limits<double>::max()};
                d_solver->setOption(
                    name, std::to_string((range.first + range.second) / 2));
              },
              [this, &name](const OptionInfo::ModeInfo& v) {
                if (!v.modes.empty())
                {
                  d_solver->setOption(name, v.modes[0]);
                }
              },
          },
          info.valueInfo);
    }
    catch (const CVC5ApiOptionException&)
    {
    }
  }
};

TEST_F(TestBlackOptions, set)
{
  const std::set<std::string> muted{"copyright",
                                    "help",
                                    "show-config",
                                    "show-debug-tags",
                                    "show-trace-tags",
                                    "version"};
  for (const auto& name : options::getNames())
  {
    if (name == "safe-mode")
    {
      // don't test safe-mode here, since it will restrict the set of options
      // that can be set afterwards.
      continue;
    }
    if (muted.count(name))
    {
      testing::internal::CaptureStdout();
    }
    testSetOption(name);
    if (muted.count(name))
    {
      testing::internal::GetCapturedStdout();
    }
  }
}

TEST_F(TestBlackOptions, setSafe)
{
  const std::set<std::string> muted{"copyright",
                                    "help",
                                    "show-config",
                                    "show-debug-tags",
                                    "show-trace-tags",
                                    "version"};
  // set safe options to true
  d_solver->setOption("safe-mode", "safe");
  bool alreadySetRegular = false;
  for (const auto& name : options::getNames())
  {
    auto info = d_solver->getOptionInfo(name);
    // skip if an expert option or has an supported feature
    if (info.category == cvc5::modes::OptionCategory::EXPERT
        || !info.noSupports.empty())
    {
      continue;
    }
    if (info.category == cvc5::modes::OptionCategory::REGULAR)
    {
      if (alreadySetRegular)
      {
        // skip if already set a regular option
        continue;
      }
      alreadySetRegular = true;
    }
    if (muted.count(name))
    {
      testing::internal::CaptureStdout();
    }
    // set the option once
    testSetOptionOnce(name);
    if (muted.count(name))
    {
      testing::internal::GetCapturedStdout();
    }
  }
}

TEST_F(TestBlackOptions, getOptionInfoBenchmark)
{
  auto names = options::getNames();
  std::unordered_set<std::string> ignore = {
    "output",
    "quiet",
    "rweight",
    "trace",
    "verbose",
  };
  auto end = std::remove_if(names.begin(), names.end(), [&](const auto& i){
      return ignore.count(i);
  });
  names.erase(end, names.end());
  size_t ct = 0;
  for (size_t i = 0; i < 1000; ++i)
  {
    for (const auto& name : names)
    {
      ct += d_solver->getOption(name).size();
    }
  }
  std::cout << ct << std::endl;
}

}  // namespace test
}  // namespace cvc5::internal
