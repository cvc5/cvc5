/*********************                                           -*- C++ -*-  */
/** context_mm_black.h
 ** Original author: dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Black box testing of CVC4::Node.
 **/

#include <cxxtest/TestSuite.h>
#include <cstring>

//Used in some of the tests
#include <vector>
#include <iostream>
#include "context/context_mm.h"

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
    int chunkSizeBytes = 16384;
    int maxFreeChunks = 100;
    int piecesPerChunk = 13;
    int len = chunkSizeBytes / piecesPerChunk; // Length of the individual block
    int N = maxFreeChunks*piecesPerChunk;
    for (int p = 0; p < 5; ++ p) {
      d_cmm->push();
      for (int i = 0; i < N; ++i) {
        char* newMem = (char*)d_cmm->newData(len);
        // We only setup the memory in the first run, the others should
        // reclaim the same memory
        if (p == 0) {
          for(int k = 0; k < len - 1; k ++)
            newMem[k] = 'a';
          newMem[len-1] = 0;
        }
        if (strlen(newMem) != len - 1) {
          cout << strlen(newMem) << " : " << len - 1 << endl;
        }
        TS_ASSERT(strlen(newMem) == len - 1);
      }
      d_cmm->pop();
    }

    int factor = 3;
    N = 16384/factor;

    // Push, then allocate, then pop all at once
    for (int p = 0; p < 5; ++ p) {
      d_cmm->push();
      for (int i = 1; i < N; ++i) {
        int len = i*factor;
        char* newMem = (char*)d_cmm->newData(len);
        for(int k = 0; k < len - 1; k ++)
          newMem[k] = 'a';
        newMem[len-1] = 0;
        TS_ASSERT(strlen(newMem) == len - 1);
      }
    }
    for (int p = 0; p < 5; ++ p) {
      d_cmm->pop();
    }

    // Try poping out of scope
    d_cmm->pop();
  }

  void tearDown() {
    delete d_cmm;
  }
};
