/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Gereon Kremer, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Black box testing of cvc5 output classes.
 */

#include <iostream>
#include <sstream>

#include "base/output.h"
#include "test.h"

namespace cvc5::internal {
namespace test {

class TestUtilBlackOutput : public TestInternal
{
 protected:
  void SetUp() override
  {
    TestInternal::SetUp();
    TraceChannel.setStream(&d_traceStream);
    WarningChannel.setStream(&d_warningStream);

    d_debugStream.str("");
    d_traceStream.str("");
    d_warningStream.str("");
  }

  int32_t failure()
  {
    // this represents an expensive function that should NOT be called
    // when debugging/tracing is turned off
    std::cout << "a function was evaluated under an output operation when it "
                 "should not have been";
    assert(false);
    return 0;
  }
  std::stringstream d_debugStream;
  std::stringstream d_traceStream;
  std::stringstream d_warningStream;
};

TEST_F(TestUtilBlackOutput, output)
{
  Warning() << "bad warning!";

  TraceChannel.on("foo");
  Trace("foo") << "tracing1";
  TraceChannel.off("foo");
  Trace("foo") << "tracing2";
  TraceChannel.on("foo");
  Trace("foo") << "tracing3";

#ifdef CVC5_MUZZLE

  ASSERT_EQ(d_warningStream.str(), "");
  ASSERT_EQ(d_traceStream.str(), "");

#else /* CVC5_MUZZLE */

  ASSERT_EQ(d_warningStream.str(), "bad warning!");

#ifdef CVC5_TRACING
  ASSERT_EQ(d_traceStream.str(), "tracing1tracing3");
#else  /* CVC5_TRACING */
  ASSERT_EQ(d_traceStream.str(), "");
#endif /* CVC5_TRACING */

#endif /* CVC5_MUZZLE */
}

TEST_F(TestUtilBlackOutput, evaluation_off_when_it_is_supposed_to_be)
{
  TraceChannel.on("foo");
#ifndef CVC5_TRACING
  ASSERT_FALSE(TraceIsOn("foo"));
  Trace("foo") << failure() << std::endl;
#else
  ASSERT_TRUE(TraceIsOn("foo"));
#endif
  TraceChannel.off("foo");

#ifdef CVC5_MUZZLE
  ASSERT_FALSE(TraceIsOn("foo"));
  ASSERT_FALSE(TraceIsOn("foo"));
  ASSERT_FALSE(Warning.isOn());

  cout << "debug" << std::endl;
  Trace("foo") << failure() << std::endl;
  cout << "trace" << std::endl;
  Trace("foo") << failure() << std::endl;
  cout << "warning" << std::endl;
  Warning() << failure() << std::endl;
#endif
}

TEST_F(TestUtilBlackOutput, simple_print)
{
#ifdef CVC5_MUZZLE

  TraceChannel.off("yo");
  Trace("yo") << "foobar";
  ASSERT_EQ(d_traceStream.str(), std::string());
  d_traceStream.str("");
  TraceChannel.on("yo");
  Trace("yo") << "baz foo";
  ASSERT_EQ(d_traceStream.str(), std::string());
  d_traceStream.str("");

  Warning() << "baz foo";
  ASSERT_EQ(d_warningStream.str(), std::string());
  d_warningStream.str("");

#else /* CVC5_MUZZLE */

  TraceChannel.off("yo");
  Trace("yo") << "foobar";
  ASSERT_EQ(d_traceStream.str(), std::string());
  d_traceStream.str("");
  TraceChannel.on("yo");
  Trace("yo") << "baz foo";
#ifdef CVC5_TRACING
  ASSERT_EQ(d_traceStream.str(), std::string("baz foo"));
#else  /* CVC5_TRACING */
  ASSERT_EQ(d_traceStream.str(), std::string());
#endif /* CVC5_TRACING */
  d_traceStream.str("");

  Warning() << "baz foo";
  ASSERT_EQ(d_warningStream.str(), std::string("baz foo"));
  d_warningStream.str("");

#endif /* CVC5_MUZZLE */
}
}  // namespace test
}  // namespace cvc5::internal
