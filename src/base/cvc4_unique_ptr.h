/*********************                                                        */
/*! \file cvc4_unique_ptr.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A CVC4 variant of unique_ptr for C++05.
 **
 ** A CVC4 variant of unique_ptr for C++05.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__UNIQUE_PTR_H
#define __CVC4__UNIQUE_PTR_H

namespace CVC4 {

/**
 * A CVC4 variant of unique_ptr for C++05.
 *
 * This is a variant of unique_ptr that is not designed for move semantics.
 * These are appropriate to own pointer allocations on the stack that should be
 * deleted when an exception is thrown. These should be used with care within
 * heap based data structures, and never as the return value of a function.
 */
template <class T>
class UniquePtr {
 public:
  UniquePtr() : d_pointer(NULL) {}
  UniquePtr(T* pointer) : d_pointer(pointer) {}
  ~UniquePtr() { delete d_pointer; }

  void reset(T* pointer) {
    delete d_pointer;
    d_pointer = pointer;
  }

  /** Gives up ownership of the pointer to the caller. */
  T* release() {
    T* copy = d_pointer;
    d_pointer = NULL;
    return copy;
  }

  /** Returns the pointer. */
  T* get() const { return d_pointer; }

  /** Returns the pointer. Undefined if the pointer is null. */
  T* operator->() const { return d_pointer; }

  /** Returns true if the pointer is not-null. */
  operator bool() const { return d_pointer != NULL; }

 private:
  UniquePtr(const UniquePtr*) CVC4_UNDEFINED;
  UniquePtr& operator=(const UniquePtr&) CVC4_UNDEFINED;

  /** An owned pointer object allocated by `new` or NULL. */
  T* d_pointer;
}; /* class UniquePtr */

} /* CVC4 namespace */

#endif /* __CVC4__UNIQUE_PTR_H */
