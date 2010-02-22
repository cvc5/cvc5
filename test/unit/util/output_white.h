/*********************                                                        */
/** output_white.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** White box testing of CVC4::Configuration.
 **/

#include <cxxtest/TestSuite.h>

#include <iostream>
#include <sstream>

#include "util/output.h"

using namespace CVC4;
using namespace std;

class OutputWhite : public CxxTest::TestSuite {

  stringstream d_debugStream;
  stringstream d_traceStream;
  stringstream d_noticeStream;
  stringstream d_chatStream;
  stringstream d_messageStream;
  stringstream d_warningStream;

public:

  void setUp() {
    Debug.setStream(d_debugStream);
    Trace.setStream(d_traceStream);
    Notice.setStream(d_noticeStream);
    Chat.setStream(d_chatStream);
    Message.setStream(d_messageStream);
    Warning.setStream(d_warningStream);
  }

  void testOutput() {
    Debug.on("foo");
    Debug("foo") << "testing1";
    Debug.off("foo");
    Debug("foo") << "testing2";
    Debug.on("foo");
    Debug("foo") << "testing3";

    Message() << "a message";
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

    TS_ASSERT( d_debugStream.str() == "" );
    TS_ASSERT( d_messageStream.str() == "" );
    TS_ASSERT( d_warningStream.str() == "" );
    TS_ASSERT( d_chatStream.str() == "" );
    TS_ASSERT( d_noticeStream.str() == "" );
    TS_ASSERT( d_traceStream.str() == "" );

#else /* CVC4_MUZZLE */

#  ifdef CVC4_DEBUG
    TS_ASSERT( d_debugStream.str() == "testing1testing3" );
#  else /* CVC4_DEBUG */
    TS_ASSERT( d_debugStream.str() == "" );
#  endif /* CVC4_DEBUG */

    TS_ASSERT( d_messageStream.str() == "a message" );
    TS_ASSERT( d_warningStream.str() == "bad warning!" );
    TS_ASSERT( d_chatStream.str() == "chatty" );
    TS_ASSERT( d_noticeStream.str() == "note" );

#  ifdef CVC4_TRACING
    TS_ASSERT( d_traceStream.str() == "tracing1tracing3" );
#  else /* CVC4_TRACING */
    TS_ASSERT( d_traceStream.str() == "" );
#  endif /* CVC4_TRACING */

#endif /* CVC4_MUZZLE */
  }

};
