/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Regression test for `theory::ff::Tracer` dangling-handler bug.
 *
 * `Tracer::setFunctionPointers()` installs four `std::function`s into CoCoA's
 * global handler slots; each captures `this`. Pre-fix `unsetFunctionPointers()`
 * only toggled `CoCoA::handlersEnabled = false` and the class had no
 * user-defined destructor, so a `Tracer` destroyed via stack unwinding left
 * the globals holding callables pointing at freed storage.
 *
 * White-box check: after a `Tracer` goes out of scope without explicit
 * cleanup, the four CoCoA global handler slots must be empty
 * `std::function`s. Pre-fix they remain non-empty (dangling); post-fix the
 * destructor clears them.
 */

#ifdef CVC5_USE_COCOA

#include <CoCoA/TmpGPoly.H>

#include "test.h"
#include "theory/ff/core.h"
#include "util/cocoa_globals.h"

namespace cvc5::internal {
namespace test {

class TestTheoryFfTracerWhite : public TestInternal
{
};

TEST_F(TestTheoryFfTracerWhite, HandlersClearedAfterDestruction)
{
  initCocoaGlobalManager();
  {
    theory::ff::Tracer tracer({});
    tracer.setFunctionPointers();
    // Intentionally do not call unsetFunctionPointers(): simulate stack
    // unwinding past the explicit cleanup.
  }
  EXPECT_FALSE(static_cast<bool>(CoCoA::sPolyHandler));
  EXPECT_FALSE(static_cast<bool>(CoCoA::reductionStartHandler));
  EXPECT_FALSE(static_cast<bool>(CoCoA::reductionStepHandler));
  EXPECT_FALSE(static_cast<bool>(CoCoA::reductionEndHandler));
  EXPECT_FALSE(CoCoA::handlersEnabled);
}

}  // namespace test
}  // namespace cvc5::internal

#endif /* CVC5_USE_COCOA */
