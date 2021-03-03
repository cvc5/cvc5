/*********************                                                        */
/*! \file output_black.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4 output classes.
 **
 ** Black box testing of CVC4 output classes.
 **/

#include <iostream>
#include <sstream>

#include "base/output.h"
#include "test.h"

namespace CVC4 {
namespace test {

class TestUtilBlackOutput : public TestInternal
{
 protected:
  void SetUp() override
  {
    TestInternal::SetUp();
    DebugChannel.setStream(&d_debugStream);
    TraceChannel.setStream(&d_traceStream);
    NoticeChannel.setStream(&d_noticeStream);
    ChatChannel.setStream(&d_chatStream);
    MessageChannel.setStream(&d_messageStream);
    WarningChannel.setStream(&d_warningStream);

    d_debugStream.str("");
    d_traceStream.str("");
    d_noticeStream.str("");
    d_chatStream.str("");
    d_messageStream.str("");
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
  std::stringstream d_noticeStream;
  std::stringstream d_chatStream;
  std::stringstream d_messageStream;
  std::stringstream d_warningStream;
};

TEST_F(TestUtilBlackOutput, output)
{
  Debug.on("foo");
  Debug("foo") << "testing1";
  Debug.off("foo");
  Debug("foo") << "testing2";
  Debug.on("foo");
  Debug("foo") << "testing3";

  CVC4Message() << "a message";
  Warning() << "bad warning!";
  Chat() << "chatty";
  Notice() << "note";

  Trace.on("foo");
  Trace("foo") << "tracing1";
  Trace.off("foo");
  Trace("foo") << "tracing2";
  Trace.on("foo");
  Trace("foo") << "tracing3";

#ifdef CVC4_MUZZLE

  ASSERT_EQ(d_debugStream.str(), "");
  ASSERT_EQ(d_messageStream.str(), "");
  ASSERT_EQ(d_warningStream.str(), "");
  ASSERT_EQ(d_chatStream.str(), "");
  ASSERT_EQ(d_noticeStream.str(), "");
  ASSERT_EQ(d_traceStream.str(), "");

#else /* CVC4_MUZZLE */

#ifdef CVC4_DEBUG
  ASSERT_EQ(d_debugStream.str(), "testing1testing3");
#else  /* CVC4_DEBUG */
  ASSERT_EQ(d_debugStream.str(), "");
#endif /* CVC4_DEBUG */

  ASSERT_EQ(d_messageStream.str(), "a message");
  ASSERT_EQ(d_warningStream.str(), "bad warning!");
  ASSERT_EQ(d_chatStream.str(), "chatty");
  ASSERT_EQ(d_noticeStream.str(), "note");

#ifdef CVC4_TRACING
  ASSERT_EQ(d_traceStream.str(), "tracing1tracing3");
#else  /* CVC4_TRACING */
  ASSERT_EQ(d_traceStream.str(), "");
#endif /* CVC4_TRACING */

#endif /* CVC4_MUZZLE */
}

TEST_F(TestUtilBlackOutput, evaluation_off_when_it_is_supposed_to_be)
{
  Debug.on("foo");
#ifndef CVC4_DEBUG
  ASSERT_FALSE(Debug.isOn("foo"));
  Debug("foo") << failure() << endl;
#else
  ASSERT_TRUE(Debug.isOn("foo"));
#endif
  Debug.off("foo");

  Trace.on("foo");
#ifndef CVC4_TRACING
  ASSERT_FALSE(Trace.isOn("foo"));
  Trace("foo") << failure() << endl;
#else
  ASSERT_TRUE(Trace.isOn("foo"));
#endif
  Trace.off("foo");

#ifdef CVC4_MUZZLE
  ASSERT_FALSE(Debug.isOn("foo"));
  ASSERT_FALSE(Trace.isOn("foo"));
  ASSERT_FALSE(Warning.isOn());
  ASSERT_FALSE(CVC4Message.isOn());
  ASSERT_FALSE(Notice.isOn());
  ASSERT_FALSE(Chat.isOn());

  cout << "debug" << std::endl;
  Debug("foo") << failure() << endl;
  cout << "trace" << std::endl;
  Trace("foo") << failure() << endl;
  cout << "warning" << std::endl;
  Warning() << failure() << endl;
  cout << "message" << std::endl;
  CVC4Message() << failure() << endl;
  cout << "notice" << std::endl;
  Notice() << failure() << endl;
  cout << "chat" << std::endl;
  Chat() << failure() << endl;
#endif
}

TEST_F(TestUtilBlackOutput, simple_print)
{
#ifdef CVC4_MUZZLE

  Debug.off("yo");
  Debug("yo") << "foobar";
  ASSERT_EQ(d_debugStream.str(), std::string());
  d_debugStream.str("");
  Debug.on("yo");
  Debug("yo") << "baz foo";
  ASSERT_EQ(d_debugStream.str(), std::string());
  d_debugStream.str("");

  Trace.off("yo");
  Trace("yo") << "foobar";
  ASSERT_EQ(d_traceStream.str(), std::string());
  d_traceStream.str("");
  Trace.on("yo");
  Trace("yo") << "baz foo";
  ASSERT_EQ(d_traceStream.str(), std::string());
  d_traceStream.str("");

  Warning() << "baz foo";
  ASSERT_EQ(d_warningStream.str(), std::string());
  d_warningStream.str("");

  Chat() << "baz foo";
  ASSERT_EQ(d_chatStream.str(), std::string());
  d_chatStream.str("");

  CVC4Message() << "baz foo";
  ASSERT_EQ(d_messageStream.str(), std::string());
  d_messageStream.str("");

  Notice() << "baz foo";
  ASSERT_EQ(d_noticeStream.str(), std::string());
  d_noticeStream.str("");

#else /* CVC4_MUZZLE */

  Debug.off("yo");
  Debug("yo") << "foobar";
  ASSERT_EQ(d_debugStream.str(), std::string());
  d_debugStream.str("");
  Debug.on("yo");
  Debug("yo") << "baz foo";
#ifdef CVC4_DEBUG
  ASSERT_EQ(d_debugStream.str(), std::string("baz foo"));
#else  /* CVC4_DEBUG */
  ASSERT_EQ(d_debugStream.str(), std::string());
#endif /* CVC4_DEBUG */
  d_debugStream.str("");

  Trace.off("yo");
  Trace("yo") << "foobar";
  ASSERT_EQ(d_traceStream.str(), std::string());
  d_traceStream.str("");
  Trace.on("yo");
  Trace("yo") << "baz foo";
#ifdef CVC4_TRACING
  ASSERT_EQ(d_traceStream.str(), std::string("baz foo"));
#else  /* CVC4_TRACING */
  ASSERT_EQ(d_traceStream.str(), std::string());
#endif /* CVC4_TRACING */
  d_traceStream.str("");

  Warning() << "baz foo";
  ASSERT_EQ(d_warningStream.str(), std::string("baz foo"));
  d_warningStream.str("");

  Chat() << "baz foo";
  ASSERT_EQ(d_chatStream.str(), std::string("baz foo"));
  d_chatStream.str("");

  CVC4Message() << "baz foo";
  ASSERT_EQ(d_messageStream.str(), std::string("baz foo"));
  d_messageStream.str("");

  Notice() << "baz foo";
  ASSERT_EQ(d_noticeStream.str(), std::string("baz foo"));
  d_noticeStream.str("");

#endif /* CVC4_MUZZLE */
}
}  // namespace test
}  // namespace CVC4
