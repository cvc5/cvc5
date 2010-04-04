/*********************                                                        */
/** cdmap_black.h
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
 ** Black box testing of CVC4::context::CDMap<>.
 **/

#include <cxxtest/TestSuite.h>

#include "context/cdmap.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;

class CDMapBlack : public CxxTest::TestSuite {

  Context* d_context;

public:

  void setUp() {
    d_context = new Context;
    //Debug.on("cdmap");
    //Debug.on("gc");
    //Debug.on("pushpop");
  }

  void tearDown() {
    delete d_context;
  }

  void testSimpleSequence() {
    CDMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());

        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());

        {
          d_context->push();

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());

          map.insert(1, 45);

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());

          d_context->pop();
        }

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());

        d_context->pop();
      }

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());

      d_context->pop();
    }

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
  }

  // no intervening find() in this one
  // (under the theory that this could trigger a bug)
  void testSimpleSequenceFewerFinds() {
    CDMap<int, int> map(d_context);

    map.insert(3, 4);

    {
      d_context->push();

      map.insert(5, 6);
      map.insert(9, 8);

      {
        d_context->push();

        map.insert(1, 2);

        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(7) == map.end());

        {
          d_context->push();

          d_context->pop();
        }

        d_context->pop();
      }

      d_context->pop();
    }
  }

  void testObliterate() {
    CDMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());

        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());

        map.obliterate(5);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) == map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());

        {
          d_context->push();

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) == map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());

          d_context->pop();
        }

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) == map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());

        d_context->pop();
      }

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());

      d_context->pop();
    }

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
  }

  void testObliteratePrimordial() {
    CDMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());

        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());

        map.obliterate(3);

        TS_ASSERT(map.find(3) == map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());

        {
          d_context->push();

          TS_ASSERT(map.find(3) == map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());

          d_context->pop();
        }

        TS_ASSERT(map.find(3) == map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());

        d_context->pop();
      }

      TS_ASSERT(map.find(3) == map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());

      d_context->pop();
    }

    TS_ASSERT(map.find(3) == map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
  }

  void testObliterateCurrent() {
    CDMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());

        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());

        map.obliterate(1);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());

        {
          d_context->push();

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) == map.end());

          d_context->pop();
        }

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());

        d_context->pop();
      }

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());

      d_context->pop();
    }

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
  }
};
