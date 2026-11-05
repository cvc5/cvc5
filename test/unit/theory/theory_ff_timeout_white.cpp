/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Regression test for finite-field Groebner-basis exception leak.
 *
 * `theory::ff::GBasisTimeout()` reads `rm->getRemainingTime()` and passes the
 * value (divided by 1000) to `CoCoA::CpuTimeLimit(sec)`. The ctor of
 * `CpuTimeLimit` rejects `interval < 0` and `interval > 1e6` by throwing
 * `CoCoA::ErrorInfo` (not `CoCoA::TimeoutException`).
 *
 * Pre-fix, `GBasisTimeout`'s `try` block only catches
 * `CoCoA::TimeoutException`, so `ErrorInfo` escapes. `CoCoA::ErrorInfo`
 * derives from `CoCoA::exception`, not `std::exception`, so even broader
 * catch sites further up the call stack miss it.
 *
 * Post-fix, the catch routes the error to `CVC5_FATAL()` with a descriptive
 * message naming CoCoA's accepted interval range. This surfaces the cause
 * (the value supplied to CpuTimeLimit was out of range) instead of masking
 * it as a timeout.
 */

#ifdef CVC5_USE_COCOA

#include <CoCoA/QuotientRing.H>
#include <CoCoA/RingZZ.H>
#include <CoCoA/SparsePolyOps-ideal.H>
#include <CoCoA/SparsePolyRing.H>
#include <CoCoA/ring.H>
#include <CoCoA/symbol.H>

#include "options/base_options.h"
#include "options/options.h"
#include "test.h"
#include "theory/ff/cocoa_util.h"
#include "util/cocoa_globals.h"
#include "util/resource_manager.h"
#include "util/statistics_registry.h"

namespace cvc5::internal {
namespace test {

class TestTheoryFfTimeoutWhite : public TestInternal
{
};

TEST_F(TestTheoryFfTimeoutWhite, GBasisTimeoutFatalsOnCpuTimeLimitErrorInfo)
{
  // Pick a per-call limit large enough that `getRemainingTime() / 1000.0`
  // exceeds CoCoA's `CpuTimeLimit` upper bound of 1e6 seconds and the ctor
  // throws `ERR::ArgTooBig`.
  Options options;
  options.write_base().perCallMillisecondLimit = 2'000'000'001;
  StatisticsRegistry stats;
  ResourceManager rm(stats, options);
  rm.beginCall();

  initCocoaGlobalManager();
  CoCoA::SparsePolyRing polyRing =
      CoCoA::NewPolyRing(CoCoA::NewZZmod(7), CoCoA::symbols("x"));
  CoCoA::ideal id = CoCoA::ideal(CoCoA::indet(polyRing, 0));

  EXPECT_DEATH(theory::ff::GBasisTimeout(id, &rm),
               "CoCoA::CpuTimeLimit accepts intervals in \\[0, 1e6\\] seconds");
}

}  // namespace test
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
