/*********************                                                        */
/*! \file memory.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
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
 **/

#include <cxxtest/TestSuite.h>

#ifndef __CVC4__TEST__MEMORY_H
#define __CVC4__TEST__MEMORY_H

#include <sys/time.h>
#include <sys/resource.h>

#include "util/cvc4_assert.h"

namespace CVC4 {
namespace test {

class WithLimitedMemory {
  rlim_t d_prevAmount;

  void remember() {
    struct rlimit rlim;
    TS_ASSERT_EQUALS(getrlimit(RLIMIT_AS, &rlim), 0);
    d_prevAmount = rlim.rlim_cur;
  }

public:

  WithLimitedMemory() {
#ifdef __APPLE__
    TS_FAIL("setrlimit() is broken on Mac, can't run memory tests.");
    AlwaysAssert(false,
                 "setrlimit() is broken on Mac, can't run memory tests.");
#endif /* __APPLE__ */
    remember();
  }

  WithLimitedMemory(rlim_t amount) {
#ifdef __APPLE__
    TS_FAIL("setrlimit() is broken on Mac, can't run memory tests.");
    AlwaysAssert(false,
                 "setrlimit() is broken on Mac, can't run memory tests.");
#endif /* __APPLE__ */
    remember();
    set(amount);
  }

  ~WithLimitedMemory() {
    set(d_prevAmount);
  }

  void set(rlim_t amount) {
    struct rlimit rlim;
    rlim.rlim_cur = amount;
    rlim.rlim_max = RLIM_INFINITY;
    TS_ASSERT_EQUALS(setrlimit(RLIMIT_AS, &rlim), 0);
  }
};

}/* CVC4::test namespace */
}/* CVC4 namespace */

#endif /* __CVC4__TEST__MEMORY_H */
