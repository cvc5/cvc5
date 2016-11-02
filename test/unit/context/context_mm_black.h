/*********************                                                        */
/*! \file context_mm_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Black box testing of CVC4::context::ContextMemoryManager.
 **
 ** Black box testing of CVC4::context::ContextMemoryManager.
 **/

#include <cxxtest/TestSuite.h>
#include <cstring>

//Used in some of the tests
#include <vector>
#include <iostream>

#include "context/context_mm.h"

#include "base/cvc4_assert.h"

using namespace std;
using namespace CVC4::context;

class ContextBlack : public CxxTest::TestSuite {
private:

  ContextMemoryManager* d_cmm;

public:

  void setUp() {
    d_cmm = new ContextMemoryManager();
  }

  void testPushPop() {

    // Push, then allocate, then pop
    // We make sure that we don't allocate too much so that all the regions
    // should be reclaimed
    unsigned chunkSizeBytes = 16384;
    unsigned maxFreeChunks = 100;
    unsigned piecesPerChunk = 13;
    unsigned len = chunkSizeBytes / piecesPerChunk; // Length of the individual block
    unsigned N = maxFreeChunks*piecesPerChunk;
    for(unsigned p = 0; p < 5; ++ p) {
      d_cmm->push();
      for(unsigned i = 0; i < N; ++i) {
        char* newMem = (char*)d_cmm->newData(len);
        // We only setup the memory in the first run, the others should
        // reclaim the same memory
        if(p == 0) {
          for(unsigned k = 0; k < len - 1; k ++) {
            newMem[k] = 'a';
          }
          newMem[len-1] = 0;
        }
        if(strlen(newMem) != len - 1) {
          cout << strlen(newMem) << " : " << len - 1 << endl;
        }
        TS_ASSERT(strlen(newMem) == len - 1);
      }
      d_cmm->pop();
    }

    unsigned factor = 3;
    N = 16384 / factor;

    // Push, then allocate, then pop all at once
    for(unsigned p = 0; p < 5; ++ p) {
      d_cmm->push();
      for(unsigned i = 1; i < N; ++i) {
        unsigned len = i * factor;
        char* newMem = (char*)d_cmm->newData(len);
        for(unsigned k = 0; k < len - 1; k ++) {
          newMem[k] = 'a';
        }
        newMem[len-1] = 0;
        TS_ASSERT(strlen(newMem) == len - 1);
      }
    }
    for(unsigned p = 0; p < 5; ++ p) {
      d_cmm->pop();
    }

    // Try popping out of scope
    TS_ASSERT_THROWS(d_cmm->pop(), CVC4::AssertionException);
  }

  void tearDown() {
    delete d_cmm;
  }
};
