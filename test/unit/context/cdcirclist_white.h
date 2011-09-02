/*********************                                                        */
/*! \file cdcirclist_white.h
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
 ** \brief White box testing of CVC4::context::CDCircList<>.
 **
 ** White box testing of CVC4::context::CDCircList<>.
 **/

#include <cxxtest/TestSuite.h>

#include <vector>
#include <iostream>

#include <limits.h>

#include "context/context.h"
#include "context/cdcirclist.h"

#include "util/output.h"

using namespace std;
using namespace CVC4::context;
using namespace CVC4;

class CDCircListWhite : public CxxTest::TestSuite {
private:

  Context* d_context;

public:

  void setUp() {
    d_context = new Context();
  }

  void tearDown() {
    delete d_context;
  }

  void testSimple() {
    //Debug.on("cdcirclist");
    CDCircList<int> l(d_context, ContextMemoryAllocator<int>(d_context->getCMM()));

    TS_ASSERT_THROWS_NOTHING( l.debugCheck() );

    d_context->push();
    {
      TS_ASSERT(l.empty());
      l.push_back(1);
      TS_ASSERT(!l.empty());
      TS_ASSERT_EQUALS(l.front(), 1);
      TS_ASSERT_EQUALS(l.back(), 1);
      TS_ASSERT_THROWS_NOTHING( l.debugCheck() );

      l.push_back(2);
      TS_ASSERT(!l.empty());
      TS_ASSERT_EQUALS(l.front(), 1);
      TS_ASSERT_EQUALS(l.back(), 2);
      TS_ASSERT_THROWS_NOTHING( l.debugCheck() );

      l.push_back(3);
      TS_ASSERT(!l.empty());
      TS_ASSERT_EQUALS(l.front(), 1);
      TS_ASSERT_EQUALS(l.back(), 3);
      TS_ASSERT_THROWS_NOTHING( l.debugCheck() );

#ifdef CVC4_ASSERTIONS
      TS_ASSERT_THROWS( l.concat(l), AssertionException );
#endif /* CVC4_ASSERTIONS */

      CDCircList<int> l2(d_context, ContextMemoryAllocator<int>(d_context->getCMM()));
      l2.push_back(4);
      l2.push_back(5);
      l2.push_back(6);
      TS_ASSERT_EQUALS(l2.front(), 4);
      TS_ASSERT_EQUALS(l2.back(), 6);
      TS_ASSERT_THROWS_NOTHING( l2.debugCheck() );

      d_context->push();
      {
        l.concat(l2);

        TS_ASSERT_EQUALS(l.front(), 1);
        TS_ASSERT_EQUALS(l.back(), 6);
        TS_ASSERT_THROWS_NOTHING( l.debugCheck() );

        TS_ASSERT_EQUALS(l2.front(), 4);
        TS_ASSERT_EQUALS(l2.back(), 3);
        TS_ASSERT_THROWS_NOTHING( l2.debugCheck() );

        d_context->push();
        {
          CDCircList<int>::iterator i = l.begin();
          CDCircList<int>::iterator j = l.begin();
          TS_ASSERT_EQUALS(i, j);
          TS_ASSERT_EQUALS(i++, j);
          TS_ASSERT_EQUALS(i, ++j);
          TS_ASSERT_EQUALS(l.erase(l.begin()), i);

          i = l.begin();
          TS_ASSERT_EQUALS(i, j); TS_ASSERT_DIFFERS(i, l.end());
          TS_ASSERT_EQUALS(*i, l.front()); TS_ASSERT_DIFFERS(i, l.end());
          TS_ASSERT_EQUALS(*i, 2); TS_ASSERT_DIFFERS(i, l.end());
          TS_ASSERT_EQUALS(*i++, 2); TS_ASSERT_DIFFERS(i, l.end()); TS_ASSERT_DIFFERS(i, j);
          TS_ASSERT_EQUALS(*i++, 3); TS_ASSERT_DIFFERS(i, l.end()); TS_ASSERT_DIFFERS(i, j);
          TS_ASSERT_EQUALS(*i++, 4); TS_ASSERT_DIFFERS(i, l.end()); TS_ASSERT_DIFFERS(i, j);
          TS_ASSERT_EQUALS(*i++, 5); TS_ASSERT_DIFFERS(i, l.end()); TS_ASSERT_DIFFERS(i, j);
          TS_ASSERT_EQUALS(*i++, 6); TS_ASSERT_EQUALS(i, l.end()); TS_ASSERT_DIFFERS(i, j);
          TS_ASSERT_EQUALS(*--i, 6); TS_ASSERT_DIFFERS(i, l.end()); TS_ASSERT_DIFFERS(i, j);
          TS_ASSERT_EQUALS(*--i, 5); TS_ASSERT_DIFFERS(i, l.end()); TS_ASSERT_DIFFERS(i, j);
          TS_ASSERT_EQUALS(*--i, 4); TS_ASSERT_DIFFERS(i, l.end()); TS_ASSERT_DIFFERS(i, j);
          TS_ASSERT_EQUALS(*--i, 3); TS_ASSERT_DIFFERS(i, l.end()); TS_ASSERT_DIFFERS(i, j);
          TS_ASSERT_EQUALS(*--i, 2); TS_ASSERT_DIFFERS(i, l.end());
          TS_ASSERT_EQUALS(i, l.begin()); TS_ASSERT_EQUALS(i, j);

          TS_ASSERT_THROWS_NOTHING( l.debugCheck() );
          TS_ASSERT_THROWS_NOTHING( l2.debugCheck() );
        }
        d_context->pop();

        CDCircList<int>::iterator i = l.begin();
        TS_ASSERT_EQUALS(*i, l.front()); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*i++, 1); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*i++, 2); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*i++, 3); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*i++, 4); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*i++, 5); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*i++, 6); TS_ASSERT_EQUALS(i, l.end());
        TS_ASSERT_EQUALS(*--i, 6); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*--i, 5); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*--i, 4); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*--i, 3); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*--i, 2); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(*--i, 1); TS_ASSERT_DIFFERS(i, l.end());
        TS_ASSERT_EQUALS(i, l.begin());

        i = l2.begin();
        TS_ASSERT_EQUALS(*i, l2.front()); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*i++, 4); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*i++, 5); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*i++, 6); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*i++, 1); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*i++, 2); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*i++, 3); TS_ASSERT_EQUALS(i, l2.end());
        TS_ASSERT_EQUALS(*--i, 3); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*--i, 2); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*--i, 1); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*--i, 6); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*--i, 5); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(*--i, 4); TS_ASSERT_DIFFERS(i, l2.end());
        TS_ASSERT_EQUALS(i, l2.begin());

        TS_ASSERT_THROWS_NOTHING( l.debugCheck() );
        TS_ASSERT_THROWS_NOTHING( l2.debugCheck() );
      }
      d_context->pop();

      TS_ASSERT(! l.empty());
      TS_ASSERT(! l2.empty());

      CDCircList<int>::iterator i = l.begin();
      TS_ASSERT_EQUALS(*i, l.front()); TS_ASSERT_DIFFERS(i, l.end());
      TS_ASSERT_EQUALS(*i++, 1); TS_ASSERT_DIFFERS(i, l.end());
      TS_ASSERT_EQUALS(*i++, 2); TS_ASSERT_DIFFERS(i, l.end());
      TS_ASSERT_EQUALS(*i++, 3); TS_ASSERT_EQUALS(i, l.end());
      TS_ASSERT_EQUALS(*--i, 3); TS_ASSERT_DIFFERS(i, l.end());
      TS_ASSERT_EQUALS(*--i, 2); TS_ASSERT_DIFFERS(i, l.end());
      TS_ASSERT_EQUALS(*--i, 1); TS_ASSERT_DIFFERS(i, l.end());
      TS_ASSERT_EQUALS(i, l.begin());

      i = l2.begin();
      TS_ASSERT_EQUALS(*i, l2.front()); TS_ASSERT_DIFFERS(i, l2.end());
      TS_ASSERT_EQUALS(*i++, 4); TS_ASSERT_DIFFERS(i, l2.end());
      TS_ASSERT_EQUALS(*i++, 5); TS_ASSERT_DIFFERS(i, l2.end());
      TS_ASSERT_EQUALS(*i++, 6); TS_ASSERT_EQUALS(i, l2.end());
      TS_ASSERT_EQUALS(*--i, 6); TS_ASSERT_DIFFERS(i, l2.end());
      TS_ASSERT_EQUALS(*--i, 5); TS_ASSERT_DIFFERS(i, l2.end());
      TS_ASSERT_EQUALS(*--i, 4); TS_ASSERT_DIFFERS(i, l2.end());
      TS_ASSERT_EQUALS(i, l2.begin());

      TS_ASSERT_THROWS_NOTHING( l.debugCheck() );
      TS_ASSERT_THROWS_NOTHING( l2.debugCheck() );
    }
    d_context->pop();

    TS_ASSERT(l.empty());
    TS_ASSERT_THROWS_NOTHING( l.debugCheck() );
  }

  void testCDPtr() {
    int* x = (int*)0x12345678;
    int* y = (int*)0x87654321;
    CDPtr<int> p(d_context, NULL);
    TS_ASSERT(p == NULL);
    d_context->push();
    TS_ASSERT(p == NULL);
    d_context->push();
    TS_ASSERT(p == NULL);
    p = x;
    TS_ASSERT(p == x);
    d_context->push();
    TS_ASSERT(p == x);
    p = y;
    TS_ASSERT(p == y);
    d_context->pop();
    TS_ASSERT(p == x);
    d_context->pop();
    TS_ASSERT(p == NULL);
    d_context->pop();
    TS_ASSERT(p == NULL);
  }

};/* class CDCircListWhite */
