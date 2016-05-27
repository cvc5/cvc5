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

  struct int_hasher {
    size_t operator()(int i) const { return i; }
  };

  struct myint {
    int x;
    myint(int i) : x(i) {}
    ~myint() { std::cout << "dtor " << x << std::endl; }
    myint& operator=(int i) { x = i; return *this; }
    bool operator==(int i) const { return x == i; }
  };

  void testMapOfLists() {
    //Debug.on("gc");
    //Debug.on("context");

    CDHashMap<int, CDList<myint>*, int_hasher> map(d_context);

    CDList<myint> *list1, *list2, *list3, *list4;

    TS_ASSERT(map.find(1) == map.end());
    TS_ASSERT(map.find(2) == map.end());
    TS_ASSERT(map.find(3) == map.end());
    TS_ASSERT(map.find(4) == map.end());

    {
      d_context->push();

      int* x CVC4_UNUSED = (int*) d_context->getCMM()->newData(sizeof(int));

      list1 = new(d_context->getCMM()) CDList<myint>(true, d_context);
      list2 = new(d_context->getCMM()) CDList<myint>(true, d_context);
      list3 = new(d_context->getCMM()) CDList<myint>(true, d_context);
      list4 = new(d_context->getCMM()) CDList<myint>(true, d_context);

      list1->push_back(1);
      list2->push_back(2);
      list3->push_back(3);
      list4->push_back(4);

      map.insertDataFromContextMemory(1, list1);
      map.insertDataFromContextMemory(2, list2);

      {
        d_context->push();

        list1->push_back(10);
        list2->push_back(20);
        list3->push_back(30);
        list4->push_back(40);

        map.insertDataFromContextMemory(3, list3);
        map.insertDataFromContextMemory(4, list4);

        x = (int*) d_context->getCMM()->newData(sizeof(int));

        TS_ASSERT(map.find(1) != map.end());
        TS_ASSERT(map.find(2) != map.end());
        TS_ASSERT(map.find(3) != map.end());
        TS_ASSERT(map.find(4) != map.end());

        TS_ASSERT(map[1] == list1);
        TS_ASSERT(map[2] == list2);
        TS_ASSERT(map[3] == list3);
        TS_ASSERT(map[4] == list4);

        TS_ASSERT((*list1)[0] == 1);
        TS_ASSERT((*list2)[0] == 2);
        TS_ASSERT((*list3)[0] == 3);
        TS_ASSERT((*list4)[0] == 4);

        TS_ASSERT((*list1)[1] == 10);
        TS_ASSERT((*list2)[1] == 20);
        TS_ASSERT((*list3)[1] == 30);
        TS_ASSERT((*list4)[1] == 40);

        TS_ASSERT(list1->size() == 2);
        TS_ASSERT(list2->size() == 2);
        TS_ASSERT(list3->size() == 2);
        TS_ASSERT(list4->size() == 2);

        d_context->pop();
      }

      TS_ASSERT(map.find(1) != map.end());
      TS_ASSERT(map.find(2) != map.end());
      TS_ASSERT(map.find(3) == map.end());
      TS_ASSERT(map.find(4) == map.end());

      TS_ASSERT(map[1] == list1);
      TS_ASSERT(map[2] == list2);

      TS_ASSERT((*list1)[0] == 1);
      TS_ASSERT((*list2)[0] == 2);
      TS_ASSERT((*list3)[0] == 3);
      TS_ASSERT((*list4)[0] == 4);

      TS_ASSERT(list1->size() == 1);
      TS_ASSERT(list2->size() == 1);
      TS_ASSERT(list3->size() == 1);
      TS_ASSERT(list4->size() == 1);

      d_context->pop();
    }

    {
      d_context->push();

      // This re-uses context memory used above.  the map.clear()
      // triggers an emptyTrash() which fails if the CDOhash_maps are put
      // in the trash.  (We use insertDataFromContextMemory() above to
      // keep them out of the trash.)
      cout << "allocating\n";
      int* x = (int*) d_context->getCMM()->newData(sizeof(int));
      cout << "x == " << x << std::endl;
      for(int i = 0; i < 1000; ++i) {
        *(int*)d_context->getCMM()->newData(sizeof(int)) = 512;
      }
      x = (int*) d_context->getCMM()->newData(sizeof(int));
      cout << "x == " << x << std::endl;

      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(2) == map.end());
      TS_ASSERT(map.find(3) == map.end());
      TS_ASSERT(map.find(4) == map.end());

      map.clear();

      TS_ASSERT(map.find(1) == map.end());
      TS_ASSERT(map.find(2) == map.end());
      TS_ASSERT(map.find(3) == map.end());
      TS_ASSERT(map.find(4) == map.end());

      d_context->pop();
    }

    TS_ASSERT(d_context->getLevel() == 0);
  }

  void testCmmElementsAtLevel0() {
    // this was crashing

    CDHashMap<int, int*, int_hasher> map(d_context);
    int* a = (int*)d_context->getCMM()->newData(sizeof(int));
    map.insertDataFromContextMemory(1, a);
  }
};
