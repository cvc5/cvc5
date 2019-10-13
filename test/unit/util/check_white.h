/*********************                                                        */
/*! \file check_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of check utilities.
 **
 ** White box testing of check utilities.
 **/

#include <cxxtest/TestSuite.h>

#include <cstring>
#include <string>

#include "base/cvc4_check.h"
#include "test_utils.h"

using namespace std;
using namespace CVC4;

namespace {

class CheckWhite : public CxxTest::TestSuite
{
 public:
  const int kOne = 1;

  // This test just checks that this statement compiles.
  std::string TerminalCvc4Fatal() const
  {
    CVC4_FATAL() << "This is a test that confirms that CVC4_FATAL can be a "
                    "terminal statement in a function that has a non-void "
                    "return type.";
  }

  void testCheck() { CVC4_CHECK(kOne >= 0) << kOne << " must be positive"; }
  void testDCheck()
  {
    CVC4_DCHECK(kOne == 1) << "always passes";
#ifndef CVC4_ASSERTIONS
    CVC4_DCHECK(false) << "Will not be compiled in when CVC4_ASSERTIONS off.";
#endif /* CVC4_ASSERTIONS */
  }

  void testPointerTypeCanBeTheCondition()
  {
    const int* one_pointer = &kOne;
    CVC4_CHECK(one_pointer);
  }

  void testExpectAbort()
  {
    TS_UTILS_EXPECT_ABORT(CVC4_CHECK(false));
    TS_UTILS_EXPECT_ABORT(CVC4_DCHECK(false));
  }
};

}  // namespace
