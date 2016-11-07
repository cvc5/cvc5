/*********************                                                        */
/*! \file memory.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utility class to help testing out-of-memory conditions.
 **
 ** Utility class to help testing out-of-memory conditions.
 **
 ** Use it like this (for example):
 **
 **   CVC4::test::WithLimitedMemory wlm(amount);
 **   TS_ASSERT_THROWS( foo(), bad_alloc );
 **
 ** The WithLimitedMemory destructor will re-establish the previous limit.
 **
 ** This class does not exist in CVC4_MEMORY_LIMITING_DISABLED is defined.
 ** This can be disabled for a variety of reasons.
 ** If this is disabled, there will be a function:
 **   void WarnWithLimitedMemoryDisabledReason()
 ** uses TS_WARN to alert users that these tests are disabled.
 **/

#include <cxxtest/TestSuite.h>

#ifndef __CVC4__TEST__MEMORY_H
#define __CVC4__TEST__MEMORY_H

#include <string>
#include <sys/resource.h>
#include <sys/time.h>

#include "base/cvc4_assert.h"

// Conditionally define CVC4_MEMORY_LIMITING_DISABLED.
#ifdef __APPLE__
#  define CVC4_MEMORY_LIMITING_DISABLED 1
#  define CVC4_MEMORY_LIMITING_DISABLED_REASON "setrlimit() is broken on Mac."
#else /* __APPLE__ */
#  if defined(__has_feature)
#    if __has_feature(address_sanitizer)
// Tests cannot expect bad_alloc to be thrown due to limit memory using
// setrlimit when ASAN is enable. ASAN instead aborts on mmap failures.
#      define CVC4_MEMORY_LIMITING_DISABLED 1
#      define CVC4_MEMORY_LIMITING_DISABLED_REASON "ASAN's mmap failures abort."
#    endif /* __has_feature(address_sanitizer) */
#  endif /* defined(__has_feature) */
#endif



namespace CVC4 {
namespace test {

#ifdef CVC4_MEMORY_LIMITING_DISABLED

inline void WarnWithLimitedMemoryDisabledReason() {
  const std::string reason = std::string("WithLimitedMemory is disabled: ") +
      std::string(CVC4_MEMORY_LIMITING_DISABLED_REASON);
  TS_WARN(reason.c_str());
}

#else /* CVC4_MEMORY_LIMITING_DISABLED */

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
    TS_ASSERT_EQUALS(setrlimit(RLIMIT_AS, &rlim), 0);
  }

 private:
  void remember() {
    struct rlimit rlim;
    TS_ASSERT_EQUALS(getrlimit(RLIMIT_AS, &rlim), 0);
    d_prevAmount = rlim.rlim_cur;
  }

  rlim_t d_prevAmount;
}; /* class WithLimitedMemory */

#endif /* CVC4_MEMORY_LIMITING_DISABLED */

} /* CVC4::test namespace */
} /* CVC4 namespace */


// Remove CVC4_MEMORY_LIMITING_DISABLED_REASON if it is defined.
#ifdef CVC4_MEMORY_LIMITING_DISABLED_REASON
#undef CVC4_MEMORY_LIMITING_DISABLED_REASON
#endif /* CVC4_MEMORY_LIMITING_DISABLED_REASON */

#endif /* __CVC4__TEST__MEMORY_H */
