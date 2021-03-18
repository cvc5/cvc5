/*********************                                                        */
/*! \file stats_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Aina Niemetz, Gereon Kremer
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::Stat and associated classes
 **
 ** Black box testing of CVC4::Stat and associated classes.
 **/

#include <iostream>
#include <string>
#include <thread>
#include <vector>

#include "api/cvc4cpp.h"
#include "expr/kind.h"
#include "test.h"
#include "theory/inference_id.h"
#include "util/statistics_reg.h"

namespace CVC4 {
namespace test {

class TestUtilBlackNewstats : public TestInternal
{
};

TEST_F(TestUtilBlackNewstats, stats)
{
  StatisticRegistry reg;
  
  TimerStats timer = reg.registerTimer("timer");
  {
    CodeTimers ct(timer);
    {
      AverageStats avg = reg.registerAverage("avg");
      avg << 1.0 << 2.0 << 17;
      std::cout << reg << std::endl;
    }
    std::this_thread::sleep_for(std::chrono::milliseconds(50));
    {
      IntStats is = reg.registerInt("foo");
      ++is++;
      is += 5;
      std::cout << reg << std::endl;
    }
  }
  {
    HistogramStats<Kind> hist = reg.registerHistogram<Kind>("hist");
    hist << Kind::PLUS << Kind::MULT << Kind::BITVECTOR_BITOF << Kind::MULT;
  }
  {
    int64_t foo;
    ReferenceStats<int64_t> ref = reg.registerReference("ref", foo);
    foo = 15;
    std::cout << reg << std::endl;
    foo = 3;
    std::cout << reg << std::endl;
  }
  {
    CodeTimers ct(timer);
    {
      std::vector<int> foo = {1,2,3,4};
      SizeStats<std::vector<int>> sstat = reg.registerSize("size", foo, false);
      foo.emplace_back(5);
      std::cout << reg << std::endl;
      std::this_thread::sleep_for(std::chrono::milliseconds(250));
      foo.emplace_back(5);
      std::cout << reg << std::endl;
    }
    {
      // re-register statistic
      HistogramStats<Kind> hist = reg.registerHistogram<Kind>("hist");
      hist << Kind::AND << Kind::OR << Kind::OR << Kind::OR;
    }
    // This crashes, because the type does not match
    // HistogramStats<theory::InferenceId> hist =
    // reg.registerHistogram<theory::InferenceId>("hist");
  }
  std::cout << reg << std::endl;

  // API
  api::Statistics stats(reg);
  std::cout << "API view: " << std::endl << stats.get("ref") << std::endl;
  std::cout << stats << std::endl;

  std::cout << "public" << std::endl;
  for (const auto& s: stats) {
    std::cout << s.first << " -> " << s.second << std::endl;
  }
  std::cout << "all" << std::endl;
  for (auto it = stats.begin_all(); it != stats.end_all(); ++it) {
    std::cout << it->first << " -> " << it->second << std::endl;
  }
  
}
}  // namespace test
}  // namespace CVC4
