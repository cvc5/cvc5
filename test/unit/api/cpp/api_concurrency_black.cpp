/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of the concurrent use of the cvc5 C++ API from several
 * threads, each with its own term manager and solver.
 */

#include <atomic>
#include <cstdint>
#include <thread>
#include <vector>

#include "test_api.h"

namespace cvc5::internal {

namespace test {

class TestApiBlackConcurrency : public TestApi
{
};

TEST_F(TestApiBlackConcurrency, solversInSeparateThreads)
{
  // Each thread creates and uses its own term manager and solver. The
  // threads synchronize right before their first assertion, so that the
  // solvers' theories (and, in builds with CoCoA support, the CoCoA global
  // manager) are initialized concurrently. Without proper synchronization
  // in the library, a thread would throw and terminate the process.
  constexpr size_t numThreads = 8;
  constexpr size_t numRounds = 5;
  for (size_t round = 0; round < numRounds; ++round)
  {
    std::atomic<size_t> ready{0};
    std::vector<int> sat(numThreads, 0);
    std::vector<std::thread> threads;
    for (size_t i = 0; i < numThreads; ++i)
    {
      threads.emplace_back([&, i]() {
        TermManager tm;
        Solver slv(tm);
        Sort intSort = tm.getIntegerSort();
        Term x = tm.mkConst(intSort, "x");
        Term bound = tm.mkInteger(static_cast<int64_t>(i));
        Term f = tm.mkTerm(Kind::GT, {x, bound});
        ++ready;
        while (ready.load() < numThreads)
        {
          std::this_thread::yield();
        }
        slv.assertFormula(f);
        sat[i] = slv.checkSat().isSat() ? 1 : 0;
      });
    }
    for (std::thread& t : threads)
    {
      t.join();
    }
    for (size_t i = 0; i < numThreads; ++i)
    {
      ASSERT_EQ(sat[i], 1) << "thread " << i << " in round " << round;
    }
  }
}

}  // namespace test
}  // namespace cvc5::internal
