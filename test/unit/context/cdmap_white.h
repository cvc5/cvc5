/*********************                                                        */
/*! \file cdmap_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::context::CDMap<>.
 **
 ** White box testing of CVC4::context::CDMap<>.
 **/

#include <cxxtest/TestSuite.h>

#include "base/cvc4_assert.h"
#include "context/cdhashmap.h"

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
