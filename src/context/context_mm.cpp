/*********************                                           -*- C++ -*-  */
/** context_mm.cpp
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Implementation of Context Memory Manaer
 **/


#include <cstdlib>
#include <vector>
#include <deque>
#include "context/context_mm.h"
#include "util/Assert.h"


namespace CVC4 {
namespace context {


void ContextMemoryManager::newChunk() {

  // Increment index to chunk list
  ++d_indexChunkList;
  Assert(d_chunkList.size() == d_indexChunkList,
         "Index should be at the end of the list");

  // Create new chunk if no free chunk available
  if (d_freePages.empty()) {
    d_chunkList.push_back((char*)malloc(chunkSizeBytes));
    if (d_chunkList.back() == NULL) {
      throw bad_alloc();
    }
  }
  // If there is a free chunk, use that
  else {
    d_chunkList.push_back(d_freePages.back());
    d_freePages.pop_back();
  }
  // Set up the current chunk pointers
  d_nextFree = d_chunkList.back();
  d_endChunk = d_nextFree + chunkSizeBytes;
}


ContextMemoryManager() : d_indexChunkList(0) {
  // Create initial chunk
  d_chunkList.push_back((char*)malloc(chunkSizeBytes));
  d_nextFree = d_chunkList.back();
  if (d_nextFree == NULL) {
    throw bad_alloc;
  }
  d_endChunk = d_nextFree + chunkSizeBytes;
}


~ContextMemoryManager() {
  // Delete all chunks
  while (!d_chunkList.empty()) {
    free(d_chunkList.back());
    d_chunkList.pop_back();
  }
  while (!d_freePages.empty()) {
    free(d_freePages.back());
    d_freePages.pop_back();
  }
}

void* newData(size_t size) {
  // Use next available free location in current chunk
  void* res = (void*)d_nextFree;
  d_nextFree += size;
  // Check if the request is too big for the chunk
  if (d_nextFree > d_endChunk) {
    newChunk();
    res = (void*)d_nextFree;
    d_nextFree += size;
    AlwaysAssert(d_nextFree <= d_endChunk,
                 "Request is bigger than memory chunk size");
  }
  return res;
}


void push() {
  // Store current state on the stack
  d_nextFreeStack.push_back(d_nextFree);
  d_endChunkStack.push_back(d_endChunk);
  d_indexChunkListStack.push_back(d_indexChunkList);
}


void pop() {
  // Restore state from stack
  d_nextFree = d_nextFreeStack.back();
  d_nextFreeStack.pop_back();
  d_endChunk = d_endChunkStack.back();
  d_endChunkStack.pop_back();

  // Free all the new chunks since the last push
  while (d_indexChunkList > d_indexChunkListStack.back()) {
    d_freePages.push_back(d_chunkList.back());
    d_chunkList.pop_back();
    --d_indexChunkList;
  }
  d_indexChunkListStack.pop_back();

  // Delete excess free chunks
  while (d_freeChunks.size() > maxFreeChunks) {
    free(d_freePages.front());
    d_freePages.pop_front();
  }
}


}/* CVC4::context namespace */

}/* CVC4 namespace */
