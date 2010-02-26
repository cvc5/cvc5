/*********************                                                        */
/** context_mm.h
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Region-based memory manager with stack-based push and pop.  Designed
 ** for use by ContextManager.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CONTEXT_MM_H
#define __CVC4__CONTEXT__CONTEXT_MM_H

#include <vector>
#include <deque>

namespace CVC4 {
namespace context {


  /**
   * Region-based memory manager for contexts.  Calls to newData provide memory
   * from the current region.  This memory will persist until the entire
   * region is deallocated (by calling pop).
   *
   * If push is called, the current region is deactivated and pushed on a
   * stack, and a new current region is created.  A subsequent call to pop
   * releases the new region and restores the top region from the stack.
   *
   */
class ContextMemoryManager {

  /**
   * Memory in regions is allocated in chunks.  This is the chunk size
   */
  static const unsigned chunkSizeBytes = 16384;

  /**
   * A list of free chunks is maintained.  This is the maximum number of
   * free chunks.
   */
  static const unsigned maxFreeChunks = 100;

  /**
   * List of all chunks that are currently active
   */
  std::vector<char*> d_chunkList;

  /**
   * Queue of free chunks (for best cache performance, LIFO order is used)
   */
  std::deque<char*> d_freeChunks;

  /**
   * Pointer to the beginning of available memory in the current chunk in
   * the current region.
   */
  char* d_nextFree;

  /**
   * Pointer to one past the last available byte in the current chunk in
   * the current region.
   */
  char* d_endChunk;

  /**
   * The index in d_chunkList of the current chunk in the current region
   */
  unsigned d_indexChunkList;

  /**
   * Part of the stack of saved regions.  This vector stores the saved value
   * of d_nextFree
   */
  std::vector<char*> d_nextFreeStack;

  /**
   * Part of the stack of saved regions.  This vector stores the saved value
   * of d_endChunk.
   */
  std::vector<char*> d_endChunkStack;

  /**
   * Part of the stack of saved regions.  This vector stores the saved value
   * of d_indexChunkList
   */
  std::vector<unsigned> d_indexChunkListStack;

  /**
   * Private method to grab a new chunk for the current region.  Uses chunk
   * from d_freeChunks if available.  Creates a new one otherwise.  Sets the
   * new chunk to be the current chunk.
   */
  void newChunk();

 public:
  /**
   * Constructor - creates an initial region and an empty stack
   */
  ContextMemoryManager();

  /**
   * Destructor - deletes all memory in all regions
   */
  ~ContextMemoryManager();

  /**
   * Allocate size bytes from the current region
   */
  void* newData(size_t size);

  /**
   * Create a new region.  Push old region on the stack.
   */
  void push();

  /**
   * Delete all memory allocated in the current region and restore the top
   * region from the stack
   */
  void pop();

}; /* class ContextMemoryManager */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CONTEXT_MM_H */
