/*********************                                                        */
/*! \file recursion_breaker_black.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Black-box testing of RecursionBreaker<T>
 **
 ** Black-box testing of RecursionBreaker<T>.
 **/

#include <iostream>
#include <string>

#include "util/recursion_breaker.h"

using namespace CVC4;
using namespace std;

class RecursionBreakerBlack : public CxxTest::TestSuite {
  int d_count;

public:

  void setUp() {
    d_count = 0;
  }

  int foo(int x) {
    RecursionBreaker<int> breaker("foo", x);
    if(breaker.isRecursion()) {
      ++d_count;
      return 0;
    }
    int xfactor = x * x;
    if(x > 0) {
      xfactor = -xfactor;
    }
    int y = foo(11 * x + xfactor);
    int z = y < 0 ? y : x * y;
    cout << "x == " << x << ", y == " << y << " ==> " << z << endl;
    return z;
  }

  void testFoo() {
    foo(5);
    TS_ASSERT( d_count == 1 );
  }

};/* class RecursionBreakerBlack */
