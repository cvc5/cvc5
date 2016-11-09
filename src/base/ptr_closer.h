/*********************                                                        */
/*! \file ptr_closer.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A class to close owned pointers in the destructor.
 **
 ** A class to close owned pointers in the destructor.
 **/

#include "cvc4_public.h"

#ifndef __CVC4__PTR_CLOSER_H
#define __CVC4__PTR_CLOSER_H

namespace CVC4 {

/**
 * A class to close owned pointers in the destructor. This plays a similar role
 * to unique_ptr, but without move semantics. This is designed to overcome the
 * lack of having unique_ptr in C++05.
 *
 * This is a variant of unique_ptr that is not designed for move semantics.
 * These are appropriate to own pointer allocations on the stack that should be
 * deleted when an exception is thrown. These should be used with care within
 * heap based data structures, and never as the return value of a function.
 */
template <class T>
class PtrCloser {
 public:
  PtrCloser() : d_pointer(NULL) {}
  explicit PtrCloser(T* pointer) : d_pointer(pointer) {}
  ~PtrCloser() { delete d_pointer; }

  /** Deletes the currently owned copy and takes ownership of pointer. */
  void reset(T* pointer = NULL) {
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
  PtrCloser(const PtrCloser*) CVC4_UNDEFINED;
  PtrCloser& operator=(const PtrCloser&) CVC4_UNDEFINED;

  /** An owned pointer object allocated by `new`. Or NULL. */
  T* d_pointer;
}; /* class PtrCloser */

} /* CVC4 namespace */

#endif /* __CVC4__PTR_CLOSER_H */
