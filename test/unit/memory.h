/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Morgan Deters, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility class to help testing out-of-memory conditions.
 *
 * Use it like this (for example):
 *
 *   cvc5::test::WithLimitedMemory wlm(amount);
 *   ASSERT_THROW( foo(), bad_alloc );
 *
 * The WithLimitedMemory destructor will re-establish the previous limit.
 *
 * This class does not exist in CVC5_MEMORY_LIMITING_DISABLED is defined.
 * This can be disabled for a variety of reasons.
 */

#include "test.h"

#ifndef __CVC5__TEST__UNIT__MEMORY_H
#define __CVC5__TEST__UNIT__MEMORY_H

#include <string>
#include <sys/resource.h>
#include <sys/time.h>

#include "base/check.h"
#include "base/configuration_private.h"

// Conditionally define CVC5_MEMORY_LIMITING_DISABLED.
#ifdef __APPLE__
#define CVC5_MEMORY_LIMITING_DISABLED 1
#define CVC5_MEMORY_LIMITING_DISABLED_REASON "setrlimit() is broken on Mac."
#else /* __APPLE__ */

// Tests cannot expect bad_alloc to be thrown due to limit memory using
// setrlimit when ASAN is enable. ASAN instead aborts on mmap failures.
#  if IS_ASAN_BUILD
#define CVC5_MEMORY_LIMITING_DISABLED 1
#define CVC5_MEMORY_LIMITING_DISABLED_REASON "ASAN's mmap failures abort."
#  endif
#endif

namespace cvc5 {
namespace test {

#ifndef CVC5_MEMORY_LIMITING_DISABLED
class WithLimitedMemory {
 public:
  WithLimitedMemory() { remember(); }

  WithLimitedMemory(rlim_t amount) {
    remember();
    set(amount);
  }

  ~WithLimitedMemory() { set(d_prevAmount); }

  void set(rlim_t amount) {
    struct rlimit rlim;
    rlim.rlim_cur = amount;
    rlim.rlim_max = RLIM_INFINITY;
    ASSERT_EQ(setrlimit(RLIMIT_AS, &rlim), 0);
  }

 private:
  void remember() {
    struct rlimit rlim;
    ASSERT_EQ(getrlimit(RLIMIT_AS, &rlim), 0);
    d_prevAmount = rlim.rlim_cur;
  }

  rlim_t d_prevAmount;
}; /* class WithLimitedMemory */
#endif

}  // namespace test
}  // namespace cvc5

// Remove CVC5_MEMORY_LIMITING_DISABLED_REASON if it is defined.
#ifdef CVC5_MEMORY_LIMITING_DISABLED_REASON
#undef CVC5_MEMORY_LIMITING_DISABLED_REASON
#endif /* CVC5_MEMORY_LIMITING_DISABLED_REASON */

#endif /* __CVC5__TEST__MEMORY_H */
