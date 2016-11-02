/*********************                                                        */
/*! \file context_mm.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Morgan Deters, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation of Context Memory Manager.
 **
 ** Implementation of Context Memory Manager
 **/


#include <cstdlib>
#include <vector>
#include <deque>
#include <new>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "context/context_mm.h"

namespace CVC4 {
namespace context {

void ContextMemoryManager::newChunk() {

  // Increment index to chunk list
  ++d_indexChunkList;
  Assert(d_chunkList.size() == d_indexChunkList,
         "Index should be at the end of the list");

  // Create new chunk if no free chunk available
  if(d_freeChunks.empty()) {
    d_chunkList.push_back((char*)malloc(chunkSizeBytes));
    if(d_chunkList.back() == NULL) {
      throw std::bad_alloc();
    }
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
}


ContextMemoryManager::~ContextMemoryManager() {
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
    AlwaysAssert(d_nextFree <= d_endChunk,
                 "Request is bigger than memory chunk size");
  }
  Debug("context") << "ContextMemoryManager::newData(" << size
                   << ") returning " << res << " at level "
                   << d_chunkList.size() << std::endl;
  return res;
}


void ContextMemoryManager::push() {
  // Store current state on the stack
  d_nextFreeStack.push_back(d_nextFree);
  d_endChunkStack.push_back(d_endChunk);
  d_indexChunkListStack.push_back(d_indexChunkList);
}


void ContextMemoryManager::pop() {
  Assert(d_nextFreeStack.size() > 0 && d_endChunkStack.size() > 0);

  // Restore state from stack
  d_nextFree = d_nextFreeStack.back();
  d_nextFreeStack.pop_back();
  d_endChunk = d_endChunkStack.back();
  d_endChunkStack.pop_back();

  // Free all the new chunks since the last push
  while(d_indexChunkList > d_indexChunkListStack.back()) {
    d_freeChunks.push_back(d_chunkList.back());
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


} /* CVC4::context namespace */
} /* CVC4 namespace */
