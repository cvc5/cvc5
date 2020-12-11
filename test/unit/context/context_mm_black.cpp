/*********************                                                        */
/*! \file context_mm_black.cpp
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

#include <cstring>
#include <iostream>
#include <vector>

#include "context/context_mm.h"
#include "test.h"

namespace CVC4 {

using namespace context;

namespace test {

class TestContextMMBlack : public TestInternal
{
 protected:
  void SetUp() override { d_cmm.reset(new ContextMemoryManager()); }
  std::unique_ptr<ContextMemoryManager> d_cmm;
};

TEST_F(TestContextMMBlack, push_pop)
{
#ifdef CVC4_DEBUG_CONTEXT_MEMORY_MANAGER
#warning "Using the debug context memory manager, omitting unit tests"
#else
  // Push, then allocate, then pop
  // We make sure that we don't allocate too much so that all the regions
  // should be reclaimed
  uint32_t chunk_size_bytes = 16384;
  uint32_t max_free_chunks = 100;
  uint32_t pieces_per_chunk = 13;
  uint32_t len;
  uint32_t n;

  len = chunk_size_bytes / pieces_per_chunk;  // Length of the individual block
  n = max_free_chunks * pieces_per_chunk;
  for (uint32_t p = 0; p < 5; ++p)
  {
    d_cmm->push();
    for (uint32_t i = 0; i < n; ++i)
    {
      char* newMem = (char*)d_cmm->newData(len);
      // We only setup the memory in the first run, the others should
      // reclaim the same memory
      if (p == 0)
      {
        for (uint32_t k = 0; k < len - 1; k++)
        {
          newMem[k] = 'a';
        }
        newMem[len - 1] = 0;
      }
      if (strlen(newMem) != len - 1)
      {
        std::cout << strlen(newMem) << " : " << len - 1 << std::endl;
      }
      ASSERT_EQ(strlen(newMem), len - 1);
    }
    d_cmm->pop();
  }

  uint32_t factor = 3;
  n = 16384 / factor;
  // Push, then allocate, then pop all at once
  for (uint32_t p = 0; p < 5; ++p)
  {
    d_cmm->push();
    for (uint32_t i = 1; i < n; ++i)
    {
      len = i * factor;
      char* newMem = (char*)d_cmm->newData(len);
      for (uint32_t k = 0; k < len - 1; k++)
      {
        newMem[k] = 'a';
      }
      newMem[len - 1] = 0;
      ASSERT_EQ(strlen(newMem), len - 1);
    }
  }
  for (uint32_t p = 0; p < 5; ++p)
  {
    d_cmm->pop();
  }

  // Try popping out of scope
  ASSERT_DEATH(d_cmm->pop(), "d_nextFreeStack.size\\(\\) > 0");
#endif
}

}  // namespace test
}  // namespace CVC4
