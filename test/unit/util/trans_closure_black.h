/*********************                                                        */
/*! \file trans_closure_black.h
 ** \verbatim
 ** Original author: Clark Barrett
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black box testing of CVC4::TransitiveClosure.
 **
 ** Black box testing of CVC4::TransitiveClosure.
 **/


#include "util/trans_closure.h"


using namespace CVC4;
using namespace CVC4::context;
using namespace std;


class TransitiveClosureBlack : public CxxTest::TestSuite {
  Context* d_context;
  TransitiveClosure* d_tc;

public:

  void setUp() {
    d_context = new Context;
    d_tc = new TransitiveClosure(d_context);
  }

  void tearDown() {
    try {
      delete d_tc;
      delete d_context;
    } catch(Exception& e) {
      Warning() << std::endl << e << std::endl;
      throw;
    }
  }

  void testSimple() {
    bool b;
    b = d_tc->addEdge(1,2);
    TS_ASSERT(!b);

    b = d_tc->addEdge(2,3);
    TS_ASSERT(!b);

    b = d_tc->addEdge(3,1);
    TS_ASSERT(b);

    b = d_tc->addEdge(2,4);
    TS_ASSERT(!b);

    b = d_tc->addEdge(2,5);
    TS_ASSERT(!b);

    b = d_tc->addEdge(4,6);
    TS_ASSERT(!b);

    b = d_tc->addEdge(6,2);
    TS_ASSERT(b);
  }


  void test1() {
    bool b;
    b = d_tc->addEdge(1,2);
    TS_ASSERT(!b);

    d_context->push();

    b = d_tc->addEdge(2,3);
    TS_ASSERT(!b);

    b = d_tc->addEdge(3,1);
    TS_ASSERT(b);

    d_context->pop();

    b = d_tc->addEdge(3,1);
    TS_ASSERT(!b);

    b = d_tc->addEdge(2,3);
    TS_ASSERT(b);

    d_context->push();

    b = d_tc->addEdge(6,4);
    TS_ASSERT(!b);

    b = d_tc->addEdge(2,6);
    TS_ASSERT(!b);

    b = d_tc->addEdge(4,1);
    TS_ASSERT(b);

    d_context->pop();

    b = d_tc->addEdge(4,1);

    TS_ASSERT(!b);
  }

  void test2() {
    bool b;
    b = d_tc->addEdge(1,2);
    TS_ASSERT(!b);
    b = d_tc->addEdge(1,3);
    TS_ASSERT(!b);
    b = d_tc->addEdge(1,4);
    TS_ASSERT(!b);
    b = d_tc->addEdge(1,5);
    TS_ASSERT(!b);
    b = d_tc->addEdge(1,6);
    TS_ASSERT(!b);
    b = d_tc->addEdge(1,7);
    TS_ASSERT(!b);
    b = d_tc->addEdge(1,8);
    TS_ASSERT(!b);
    b = d_tc->addEdge(1,9);
    TS_ASSERT(!b);

    b = d_tc->addEdge(3,2);
    TS_ASSERT(!b);
    b = d_tc->addEdge(4,7);
    TS_ASSERT(!b);
    
    b = d_tc->addEdge(2,1);
    TS_ASSERT(b);
    b = d_tc->addEdge(3,1);
    TS_ASSERT(b);
    b = d_tc->addEdge(4,1);
    TS_ASSERT(b);
    b = d_tc->addEdge(5,1);
    TS_ASSERT(b);
    b = d_tc->addEdge(6,1);
    TS_ASSERT(b);
    b = d_tc->addEdge(7,1);
    TS_ASSERT(b);
    b = d_tc->addEdge(8,1);
    TS_ASSERT(b);
    b = d_tc->addEdge(9,1);
    TS_ASSERT(b);
  }

};/* class TransitiveClosureBlack */
