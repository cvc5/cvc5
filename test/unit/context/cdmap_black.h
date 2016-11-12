/*********************                                                        */
/*! \file cdmap_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::CDMap<>.
 **
 ** Black box testing of CVC4::context::CDMap<>.
 **/

#include <cxxtest/TestSuite.h>

#include "context/cdhashmap.h"
#include "context/cdlist.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;

class CDMapBlack : public CxxTest::TestSuite {

  Context* d_context;

public:

  void setUp() {
    d_context = new Context;
    //Debug.on("context");
    //Debug.on("gc");
    //Debug.on("pushpop");
  }

  void tearDown() {
    delete d_context;
  }

  void testSimpleSequence() {
    CDHashMap<int, int> map(d_context);

    TS_ASSERT(map.find(3) == map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(23) == map.end());

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(23) == map.end());
    TS_ASSERT(map[3] == 4);

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);

        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);

        {
          d_context->push();

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());
          TS_ASSERT(map.find(23) == map.end());
          TS_ASSERT(map[3] == 4);
          TS_ASSERT(map[5] == 6);
          TS_ASSERT(map[9] == 8);
          TS_ASSERT(map[1] == 2);

          map.insertAtContextLevelZero(23, 317);
          map.insert(1, 45);

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());
          TS_ASSERT(map.find(23) != map.end());
          TS_ASSERT(map[3] == 4);
          TS_ASSERT(map[5] == 6);
          TS_ASSERT(map[9] == 8);
          TS_ASSERT(map[1] == 45);
          TS_ASSERT(map[23] == 317);

          map.insert(23, 324);

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());
          TS_ASSERT(map.find(23) != map.end());
          TS_ASSERT(map[3] == 4);
          TS_ASSERT(map[5] == 6);
          TS_ASSERT(map[9] == 8);
          TS_ASSERT(map[1] == 45);
          TS_ASSERT(map[23] == 324);

          d_context->pop();
        }

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 317);

        d_context->pop();
      }

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) != map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);
      TS_ASSERT(map[23] == 317);

      d_context->pop();
    }

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(23) != map.end());
    TS_ASSERT(map[3] == 4);
    TS_ASSERT(map[23] == 317);
  }

  // no intervening find() in this one
  // (under the theory that this could trigger a bug)
  void testSimpleSequenceFewerFinds() {
    CDHashMap<int, int> map(d_context);

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
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[5] == 6);

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
    CDHashMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(23) == map.end());
    TS_ASSERT(map[3] == 4);

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);

        map.insertAtContextLevelZero(23, 317);
        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 317);

        map.obliterate(5);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) == map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 317);

        {
          d_context->push();

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) == map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());
          TS_ASSERT(map.find(23) != map.end());
          TS_ASSERT(map[3] == 4);
          TS_ASSERT(map[9] == 8);
          TS_ASSERT(map[1] == 2);
          TS_ASSERT(map[23] == 317);

          d_context->pop();
        }

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) == map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 317);

        map.obliterate(23);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) == map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);

        d_context->pop();
      }

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[9] == 8);

      d_context->pop();
    }

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(23) == map.end());
    TS_ASSERT(map[3] == 4);
  }

  void testObliteratePrimordial() {
    CDHashMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map[3] == 4);

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map[3] == 4);

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);

        map.obliterate(3);

        TS_ASSERT(map.find(3) == map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);

        {
          d_context->push();

          TS_ASSERT(map.find(3) == map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());
          TS_ASSERT(map[5] == 6);
          TS_ASSERT(map[9] == 8);
          TS_ASSERT(map[1] == 2);

          d_context->pop();
        }

        TS_ASSERT(map.find(3) == map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);

        d_context->pop();
      }

      TS_ASSERT(map.find(3) == map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);

      d_context->pop();
    }

    TS_ASSERT(map.find(3) == map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
  }

  void testObliterateCurrent() {
    CDHashMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map[3] == 4);

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map[3] == 4);

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);

        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);

        map.obliterate(1);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);

        {
          d_context->push();

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) == map.end());
          TS_ASSERT(map[3] == 4);
          TS_ASSERT(map[5] == 6);
          TS_ASSERT(map[9] == 8);

          d_context->pop();
        }

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);

        d_context->pop();
      }

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);

      d_context->pop();
    }

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map[3] == 4);
  }

  void testInsertAtContextLevelZero() {
    CDHashMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(23) == map.end());
    TS_ASSERT(map[3] == 4);

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);

        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);

        map.insertAtContextLevelZero(23, 317);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 317);

        TS_ASSERT_THROWS(map.insertAtContextLevelZero(23, 317),
                         AssertionException);
        TS_ASSERT_THROWS(map.insertAtContextLevelZero(23, 472),
                         AssertionException);
        map.insert(23, 472);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 472);

        {
          d_context->push();

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());
          TS_ASSERT(map.find(23) != map.end());
          TS_ASSERT(map[3] == 4);
          TS_ASSERT(map[5] == 6);
          TS_ASSERT(map[9] == 8);
          TS_ASSERT(map[1] == 2);
          TS_ASSERT(map[23] == 472);

          TS_ASSERT_THROWS(map.insertAtContextLevelZero(23, 0),
                           AssertionException);
          map.insert(23, 1024);

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());
          TS_ASSERT(map.find(23) != map.end());
          TS_ASSERT(map[3] == 4);
          TS_ASSERT(map[5] == 6);
          TS_ASSERT(map[9] == 8);
          TS_ASSERT(map[1] == 2);
          TS_ASSERT(map[23] == 1024);

          d_context->pop();
        }

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 472);

        d_context->pop();
      }

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) != map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);
      TS_ASSERT(map[23] == 317);

      TS_ASSERT_THROWS(map.insertAtContextLevelZero(23, 0),
                       AssertionException);
      map.insert(23, 477);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) != map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);
      TS_ASSERT(map[23] == 477);

      d_context->pop();
    }

    TS_ASSERT_THROWS(map.insertAtContextLevelZero(23, 0),
                     AssertionException);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(23) != map.end());
    TS_ASSERT(map[3] == 4);
    TS_ASSERT(map[23] == 317);
  }

  void testObliterateInsertedAtContextLevelZero() {
    CDHashMap<int, int> map(d_context);

    map.insert(3, 4);

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(23) == map.end());
    TS_ASSERT(map[3] == 4);

    {
      d_context->push();

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) == map.end());
      TS_ASSERT(map.find(9) == map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);

      map.insert(5, 6);
      map.insert(9, 8);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);

      {
        d_context->push();

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) == map.end());
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);

        map.insert(1, 2);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);

        map.insertAtContextLevelZero(23, 317);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 317);

        TS_ASSERT_THROWS(map.insertAtContextLevelZero(23, 317),
                         AssertionException);
        TS_ASSERT_THROWS(map.insertAtContextLevelZero(23, 472),
                         AssertionException);
        map.insert(23, 472);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 472);

        {
          d_context->push();

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());
          TS_ASSERT(map.find(23) != map.end());
          TS_ASSERT(map[3] == 4);
          TS_ASSERT(map[5] == 6);
          TS_ASSERT(map[9] == 8);
          TS_ASSERT(map[1] == 2);
          TS_ASSERT(map[23] == 472);

          TS_ASSERT_THROWS(map.insertAtContextLevelZero(23, 0),
                           AssertionException);
          map.insert(23, 1024);

          TS_ASSERT(map.find(3) != map.end());
          TS_ASSERT(map.find(5) != map.end());
          TS_ASSERT(map.find(9) != map.end());
          TS_ASSERT(map.find(1) != map.end());
          TS_ASSERT(map.find(23) != map.end());
          TS_ASSERT(map[3] == 4);
          TS_ASSERT(map[5] == 6);
          TS_ASSERT(map[9] == 8);
          TS_ASSERT(map[1] == 2);
          TS_ASSERT(map[23] == 1024);

          d_context->pop();
        }

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) != map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);
        TS_ASSERT(map[23] == 472);

        map.obliterate(23);

        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(5) != map.end());
        TS_ASSERT(map.find(9) != map.end());
        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(23) == map.end());
        TS_ASSERT(map[3] == 4);
        TS_ASSERT(map[5] == 6);
        TS_ASSERT(map[9] == 8);
        TS_ASSERT(map[1] == 2);

        d_context->pop();
      }

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) == map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);

      // reinsert as a normal map entry
      map.insert(23, 477);

      TS_ASSERT(map.find(3) != map.end());
      TS_ASSERT(map.find(5) != map.end());
      TS_ASSERT(map.find(9) != map.end());
      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(23) != map.end());
      TS_ASSERT(map[3] == 4);
      TS_ASSERT(map[5] == 6);
      TS_ASSERT(map[9] == 8);
      TS_ASSERT(map[23] == 477);

      d_context->pop();
    }

    TS_ASSERT(map.find(3) != map.end());
    TS_ASSERT(map.find(5) == map.end());
    TS_ASSERT(map.find(9) == map.end());
    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(23) == map.end());
    TS_ASSERT(map[3] == 4);
  }
};
