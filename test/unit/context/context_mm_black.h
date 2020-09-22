/*********************                                                        */
/*! \file context_mm_black.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Aina Niemetz, Andres Noetzli
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
#include "test_utils.h"

using namespace std;
using namespace CVC4::context;

class ContextBlack : public CxxTest::TestSuite {
private:

  ContextMemoryManager* d_cmm;

 public:
  void setUp() override { d_cmm = new ContextMemoryManager(); }

  void testPushPop()
  {
#ifdef CVC4_DEBUG_CONTEXT_MEMORY_MANAGER
#warning "Using the debug context memory manager, omitting unit tests"
#else
    // Push, then allocate, then pop
    // We make sure that we don't allocate too much so that all the regions
    // should be reclaimed
    uint32_t chunkSizeBytes = 16384;
    uint32_t maxFreeChunks = 100;
    uint32_t piecesPerChunk = 13;
    uint32_t len;
    uint32_t N;

    len = chunkSizeBytes / piecesPerChunk;  // Length of the individual block
    N = maxFreeChunks * piecesPerChunk;
    for (uint32_t p = 0; p < 5; ++p)
    {
      d_cmm->push();
      for (uint32_t i = 0; i < N; ++i)
      {
        char* newMem = (char*)d_cmm->newData(len);
        // We only setup the memory in the first run, the others should
        // reclaim the same memory
        if(p == 0) {
          for (uint32_t k = 0; k < len - 1; k++)
          {
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

    uint32_t factor = 3;
    N = 16384 / factor;
    // Push, then allocate, then pop all at once
    for (uint32_t p = 0; p < 5; ++p)
    {
      d_cmm->push();
      for (uint32_t i = 1; i < N; ++i)
      {
        len = i * factor;
        char* newMem = (char*)d_cmm->newData(len);
        for (uint32_t k = 0; k < len - 1; k++)
        {
          newMem[k] = 'a';
        }
        newMem[len - 1] = 0;
        TS_ASSERT(strlen(newMem) == len - 1);
      }
    }
    for (uint32_t p = 0; p < 5; ++p)
    {
      d_cmm->pop();
    }

    // Try popping out of scope
    TS_UTILS_EXPECT_ABORT(d_cmm->pop());
#endif /* __CVC4__CONTEXT__CONTEXT_MM_H */
  }

  void tearDown() override { delete d_cmm; }
};
