/******************************************************************************
 * Top contributors (to current version):
 *   Clark Barrett, Andres Noetzli, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of Context Memory Manager
 */

#include <cstdlib>
#include <deque>
#include <limits>
#include <new>
#include <ostream>
#include <vector>

#ifdef CVC5_VALGRIND
#include <valgrind/memcheck.h>
#endif /* CVC5_VALGRIND */

#include "base/check.h"
#include "base/output.h"
#include "context/context_mm.h"

namespace cvc5 {
namespace context {

#ifndef CVC5_DEBUG_CONTEXT_MEMORY_MANAGER

void ContextMemoryManager::newChunk() {

  // Increment index to chunk list
  ++d_indexChunkList;
  Assert(d_chunkList.size() == d_indexChunkList)
      << "Index should be at the end of the list";

  // Create new chunk if no free chunk available
  if(d_freeChunks.empty()) {
    d_chunkList.push_back((char*)malloc(chunkSizeBytes));
    if(d_chunkList.back() == NULL) {
      throw std::bad_alloc();
    }

#ifdef CVC5_VALGRIND
    VALGRIND_MAKE_MEM_NOACCESS(d_chunkList.back(), chunkSizeBytes);
#endif /* CVC5_VALGRIND */
  }
  // If there is a free chunk, use that
  else {
    d_chunkList.push_back(d_freeChunks.back());
    d_freeChunks.pop_back();
  }
  // Set up the current chunk pointers
  d_nextFree = d_chunkList.back();
  d_endChunk = d_nextFree + chunkSizeBytes;
}


ContextMemoryManager::ContextMemoryManager() : d_indexChunkList(0) {
  // Create initial chunk
  d_chunkList.push_back((char*)malloc(chunkSizeBytes));
  d_nextFree = d_chunkList.back();
  if(d_nextFree == NULL) {
    throw std::bad_alloc();
  }
  d_endChunk = d_nextFree + chunkSizeBytes;

#ifdef CVC5_VALGRIND
  VALGRIND_CREATE_MEMPOOL(this, 0, false);
  VALGRIND_MAKE_MEM_NOACCESS(d_nextFree, chunkSizeBytes);
  d_allocations.push_back(std::vector<char*>());
#endif /* CVC5_VALGRIND */
}


ContextMemoryManager::~ContextMemoryManager() {
#ifdef CVC5_VALGRIND
  VALGRIND_DESTROY_MEMPOOL(this);
#endif /* CVC5_VALGRIND */

  // Delete all chunks
  while(!d_chunkList.empty()) {
    free(d_chunkList.back());
    d_chunkList.pop_back();
  }
  while(!d_freeChunks.empty()) {
    free(d_freeChunks.back());
    d_freeChunks.pop_back();
  }
}


void* ContextMemoryManager::newData(size_t size) {
  // Use next available free location in current chunk
  void* res = (void*)d_nextFree;
  d_nextFree += size;
  // Check if the request is too big for the chunk
  if(d_nextFree > d_endChunk) {
    newChunk();
    res = (void*)d_nextFree;
    d_nextFree += size;
    AlwaysAssert(d_nextFree <= d_endChunk)
        << "Request is bigger than memory chunk size";
  }
  Debug("context") << "ContextMemoryManager::newData(" << size
                   << ") returning " << res << " at level "
                   << d_chunkList.size() << std::endl;

#ifdef CVC5_VALGRIND
  VALGRIND_MEMPOOL_ALLOC(this, static_cast<char*>(res), size);
  d_allocations.back().push_back(static_cast<char*>(res));
#endif /* CVC5_VALGRIND */

  return res;
}


void ContextMemoryManager::push() {
#ifdef CVC5_VALGRIND
  d_allocations.push_back(std::vector<char*>());
#endif /* CVC5_VALGRIND */

  // Store current state on the stack
  d_nextFreeStack.push_back(d_nextFree);
  d_endChunkStack.push_back(d_endChunk);
  d_indexChunkListStack.push_back(d_indexChunkList);
}


void ContextMemoryManager::pop() {
#ifdef CVC5_VALGRIND
  for (auto allocation : d_allocations.back())
  {
    VALGRIND_MEMPOOL_FREE(this, allocation);
  }
  d_allocations.pop_back();
#endif /* CVC5_VALGRIND */

  Assert(d_nextFreeStack.size() > 0 && d_endChunkStack.size() > 0);

  // Restore state from stack
  d_nextFree = d_nextFreeStack.back();
  d_nextFreeStack.pop_back();
  d_endChunk = d_endChunkStack.back();
  d_endChunkStack.pop_back();

  // Free all the new chunks since the last push
  while(d_indexChunkList > d_indexChunkListStack.back()) {
    d_freeChunks.push_back(d_chunkList.back());
#ifdef CVC5_VALGRIND
    VALGRIND_MAKE_MEM_NOACCESS(d_chunkList.back(), chunkSizeBytes);
#endif /* CVC5_VALGRIND */
    d_chunkList.pop_back();
    --d_indexChunkList;
  }
  d_indexChunkListStack.pop_back();

  // Delete excess free chunks
  while(d_freeChunks.size() > maxFreeChunks) {
    free(d_freeChunks.front());
    d_freeChunks.pop_front();
  }
}
#else

unsigned ContextMemoryManager::getMaxAllocationSize()
{
  return std::numeric_limits<unsigned>::max();
}

#endif /* CVC5_DEBUG_CONTEXT_MEMORY_MANAGER */

}  // namespace context
}  // namespace cvc5
