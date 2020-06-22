/*********************                                                        */
/*! \file cdmap_white.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief White box testing of CVC4::context::CDMap<>.
 **
 ** White box testing of CVC4::context::CDMap<>.
 **/

#include <cxxtest/TestSuite.h>

#include "base/check.h"
#include "context/cdhashmap.h"
#include "test_utils.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;

class CDMapWhite : public CxxTest::TestSuite {

  Context* d_context;

 public:
  void setUp() override { d_context = new Context; }

  void tearDown() override { delete d_context; }

  void testUnreachableSaveAndRestore()
  {
    CDHashMap<int, int> map(d_context);

    TS_ASSERT_THROWS_NOTHING(map.makeCurrent());

    TS_UTILS_EXPECT_ABORT(map.update());

    TS_UTILS_EXPECT_ABORT(map.save(d_context->getCMM()));
    TS_UTILS_EXPECT_ABORT(map.restore(&map));

    d_context->push();
    TS_UTILS_EXPECT_ABORT(map.makeCurrent());
  }
};
