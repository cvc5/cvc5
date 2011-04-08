/*********************                                                        */
/*! \file trans_closure_black.h
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
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
    //Debug.on("cc");
    // add terms, then add equalities

    bool b;
    b = d_tc->addEdge(1,2);
    TS_ASSERT(!b);

    b = d_tc->addEdge(2,3);
    TS_ASSERT(!b);

    b = d_tc->addEdge(3,1);
    TS_ASSERT(b);
  }


};/* class TransitiveClosureBlack */
