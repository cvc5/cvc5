/*********************                                                        */
/*! \file cdmap_white.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief White box testing of CVC4::context::CDMap<>.
 **
 ** White box testing of CVC4::context::CDMap<>.
 **/

#include <cxxtest/TestSuite.h>

#include "context/cdhashmap.h"
#include "util/cvc4_assert.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;

class CDMapWhite : public CxxTest::TestSuite {

  Context* d_context;

public:

  void setUp() {
    d_context = new Context;
  }

  void tearDown() {
    delete d_context;
  }

  void testUnreachableSaveAndRestore() {
    CDHashMap<int, int> map(d_context);

    TS_ASSERT_THROWS_NOTHING(map.makeCurrent());

    TS_ASSERT_THROWS(map.update(), UnreachableCodeException);

    TS_ASSERT_THROWS(map.save(d_context->getCMM()), UnreachableCodeException);
    TS_ASSERT_THROWS(map.restore(&map), UnreachableCodeException);

    d_context->push();
    TS_ASSERT_THROWS(map.makeCurrent(), UnreachableCodeException);
  }
};
