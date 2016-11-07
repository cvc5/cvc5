/*********************                                                        */
/*! \file cdvector_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include <cxxtest/TestSuite.h>

#include <vector>
#include <iostream>

#include <limits.h>

#include "context/context.h"
#include "context/cdvector.h"

using namespace std;
using namespace CVC4::context;

struct DtorSensitiveObject {
  bool& d_dtorCalled;
  DtorSensitiveObject(bool& dtorCalled) : d_dtorCalled(dtorCalled) {}
  ~DtorSensitiveObject() { d_dtorCalled = true; }
};



class CDListBlack : public CxxTest::TestSuite {
private:

  Context* d_context;

public:

  void setUp() {
    d_context = new Context();
  }

  void tearDown() {
    delete d_context;
  }

  void testCDVector17() { vectorTest(17); }
  void testCDVector31() { vectorTest(31); }
  void testCDVector191() { vectorTest(113); }

  void vectorTest(unsigned P){
    vectorTest(P, 2);
    vectorTest(P, 5);
    vectorTest(P, P/3 + 1);
  }

  void vectorTest(unsigned P, unsigned m){
    for(unsigned g=2; g< P; g++){
      vectorTest(P, g, m, 1);
      vectorTest(P, g, m, 3);
    }
  }
  vector<unsigned> copy(CDVector<unsigned>& v){
    vector<unsigned> ret;
    for(unsigned i=0; i < v.size(); ++i){
      ret.push_back(v[i]);
    }
    return ret;
  }

  void equal(vector<unsigned>& copy, CDVector<unsigned>& v){
    TS_ASSERT_EQUALS(copy.size(), v.size());
    for(unsigned i = 0; i < v.size(); ++i){
      TS_ASSERT_EQUALS(copy[i], v[i]);
    }
  }

  void vectorTest(unsigned P, unsigned g, unsigned m, unsigned r) {
    CDVector<unsigned> vec(d_context);
    vector< vector<unsigned> > copies;

    copies.push_back( copy(vec) );
    d_context->push();

    TS_ASSERT(vec.empty());
    for(unsigned i = 0; i < P; ++i){
      vec.push_back(i);
      TS_ASSERT_EQUALS(vec.size(), i+1);
    }
    TS_ASSERT(!vec.empty());
    TS_ASSERT_EQUALS(vec.size(), P);

    copies.push_back( copy(vec) );
    d_context->push();

    for(unsigned i = 0, g_i = 1; i < r*P; ++i, g_i = (g_i * g)% P){
      if(i % m == 0){
        copies.push_back( copy(vec) );
        d_context->push();
      }

      vec.set(g_i, i);

      TS_ASSERT_EQUALS(vec.get(g_i), i);
    }
    TS_ASSERT_EQUALS(vec.size(),  P);

    copies.push_back( copy(vec) );

    while(d_context->getLevel() >= 1){
      TS_ASSERT_EQUALS(vec.size(), P);
      equal(copies[d_context->getLevel()], vec);
      d_context->pop();
    }
  }

  void testTreeUpdate() {
    CDVector<int> vec(d_context);
    vec.push_back(-1);

    vec.set(0, 0);
    d_context->push();
    d_context->push();
    vec.set(0, 1);
    d_context->pop();
    d_context->pop();

    d_context->push();
    d_context->push();
    TS_ASSERT_EQUALS(vec.get(0), 0);
  }

};
