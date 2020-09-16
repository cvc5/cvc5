/*********************                                                        */
/*! \file context_mm.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Andres Noetzli, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Region-based memory manager with stack-based push and pop.
 **
 ** Region-based memory manager with stack-based push and pop.  Designed
 ** for use by ContextManager.
 **/

#include "cvc4_private.h"

#ifndef CVC4__CONTEXT__CONTEXT_MM_H
#define CVC4__CONTEXT__CONTEXT_MM_H

#include <deque>
#include <limits>
#include <vector>

namespace CVC4 {
namespace context {

#ifndef CVC4_DEBUG_CONTEXT_MEMORY_MANAGER

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

#ifdef CVC4_VALGRIND
  /**
   * Vector of allocations for each level. Used for accurately marking
   * allocations as free'd in Valgrind.
   */
  std::vector<std::vector<char*>> d_allocations;
#endif

 public:
  /**
   * Get the maximum allocation size for this memory manager.
   */
  static unsigned getMaxAllocationSize() {
    return chunkSizeBytes;
  }

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

};/* class ContextMemoryManager */

#else /* CVC4_DEBUG_CONTEXT_MEMORY_MANAGER */

#warning \
    "Using the debug version of ContextMemoryManager, expect performance degradation"

/**
 * Dummy implementation of the ContextMemoryManager for debugging purposes. Use
 * the configure flag "--enable-debug-context-memory-manager" to use this
 * implementation.
 */
class ContextMemoryManager
{
 public:
  static unsigned getMaxAllocationSize()
  {
    return std::numeric_limits<unsigned>::max();
  }

  ContextMemoryManager() { d_allocations.push_back(std::vector<char*>()); }
  ~ContextMemoryManager()
  {
    for (const auto& levelAllocs : d_allocations)
    {
      for (auto alloc : levelAllocs)
      {
        free(alloc);
      }
    }
  }

  void* newData(size_t size)
  {
    void* alloc = malloc(size);
    d_allocations.back().push_back(static_cast<char*>(alloc));
    return alloc;
  }

  void push() { d_allocations.push_back(std::vector<char*>()); }

  void pop()
  {
    for (auto alloc : d_allocations.back())
    {
      free(alloc);
    }
    d_allocations.pop_back();
  }

 private:
  std::vector<std::vector<char*>> d_allocations;
}; /* ContextMemoryManager */

#endif /* CVC4_DEBUG_CONTEXT_MEMORY_MANAGER */

/**
 * An STL-like allocator class for allocating from context memory.
 */
template <class T>
class ContextMemoryAllocator {
  ContextMemoryManager* d_mm;

public:

  typedef size_t size_type;
  typedef std::ptrdiff_t difference_type;
  typedef T* pointer;
  typedef T const* const_pointer;
  typedef T& reference;
  typedef T const& const_reference;
  typedef T value_type;
  template <class U> struct rebind {
    typedef ContextMemoryAllocator<U> other;
  };

  ContextMemoryAllocator(ContextMemoryManager* mm) : d_mm(mm) {}
  template <class U>
  ContextMemoryAllocator(const ContextMemoryAllocator<U>& alloc)
      : d_mm(alloc.getCMM())
  {
  }
  ~ContextMemoryAllocator() {}

  ContextMemoryManager* getCMM() const { return d_mm; }
  T* address(T& v) const { return &v; }
  T const* address(T const& v) const { return &v; }
  size_t max_size() const
  {
    return ContextMemoryManager::getMaxAllocationSize() / sizeof(T);
  }
  T* allocate(size_t n, const void* = 0) const {
    return static_cast<T*>(d_mm->newData(n * sizeof(T)));
  }
  void deallocate(T* p, size_t n) const {
    /* no explicit delete */
  }
  void construct(T* p, T const& v) const {
    ::new(reinterpret_cast<void*>(p)) T(v);
  }
  void destroy(T* p) const {
    p->~T();
  }
};/* class ContextMemoryAllocator<T> */

template <class T>
inline bool operator==(const ContextMemoryAllocator<T>& a1,
                       const ContextMemoryAllocator<T>& a2) {
  return a1.d_mm == a2.d_mm;
}

template <class T>
inline bool operator!=(const ContextMemoryAllocator<T>& a1,
                       const ContextMemoryAllocator<T>& a2) {
  return a1.d_mm != a2.d_mm;
}

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* CVC4__CONTEXT__CONTEXT_MM_H */
