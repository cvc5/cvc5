/*********************                                                        */
/*! \file dynamic_array.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UTIL__DYNAMIC_ARRAY_H
#define __CVC4__UTIL__DYNAMIC_ARRAY_H

#include "base/cvc4_assert.h"

namespace CVC4 {

template <class T>
class DynamicArray {
protected:
  T* d_arr;
  unsigned d_size;
  unsigned d_allocated;

  bool d_callDestructor;

  void grow() {
    bool empty = (d_arr == NULL);
    d_allocated = empty ? 15 : d_allocated * 2 + 1;
    unsigned allocSize = sizeof(T) * d_allocated;
    T* tmpList = (T*) (empty ? malloc(allocSize) :realloc(d_arr, allocSize));
    if(tmpList == NULL) {
      throw std::bad_alloc();
    }
    d_arr = tmpList;
  }

public:
  DynamicArray(bool callDestructor = false) :
    d_arr(NULL),
    d_size(0),
    d_allocated(0),
    d_callDestructor(callDestructor) {
  }

  virtual ~DynamicArray() {
    if(d_callDestructor) {
      for(unsigned i = 0; i < d_size; ++i) {
        d_arr[i].~T();
      }
    }
    free(d_arr);
  }


  unsigned size() const{
    return d_size;
  }

  bool empty() const{
    return size() == 0;
  }

  void push_back(const T& data) {
    if(d_size == d_allocated) {
      grow();
    }
    Assert(d_size < d_allocated);

    ::new((void*)(d_arr + d_size)) T(data);
    ++d_size;
  }

  const T& operator[](unsigned i) const {
    Assert(i < d_size, "index out of bounds in DynamicArray::operator[]");
    return d_arr[i];
  }

  T& operator[](unsigned i) {
    Assert(i < d_size, "index out of bounds in DynamicArray::operator[]");
    return d_arr[i];
  }

  const T& back() const {
    Assert(d_size > 0, "DynamicArray::back() called on empty list");
    return d_arr[d_size - 1];
  }

  void pop_back() {
    Assert(d_size > 0, "DynamicArray::back() called on empty list");
    --d_size;
    if(d_callDestructor) {
      d_arr[d_size].~T();
    }
  }

  typedef T* iterator;
  typedef const T* const_iterator;

  iterator begin() { return d_arr; }
  iterator end() { return d_arr + d_size; }
  const_iterator begin() const { return d_arr; }
  const_iterator end() const { return d_arr + d_size; }

};/* class DynamicArray<T> */

template <class T, class Ctor = T>
class DynamicGrowingArray : public DynamicArray<T> {
  Ctor d_ctor;

public:
  DynamicGrowingArray(bool callDestructor, const Ctor& c) :
    DynamicArray<T>(callDestructor),
    d_ctor(c) {
  }

  DynamicGrowingArray(bool callDestructor = false) :
    DynamicArray<T>(callDestructor),
    d_ctor() {
  }

  T& operator[](unsigned i) {
    while(this->d_allocated <= i) {
      this->grow();
    }
    while(this->d_size <= i) {
      ::new((void*)(this->d_arr + this->d_size)) T(d_ctor);
      ++this->d_size;
    }
    return this->d_arr[i];
  }

  const T& operator[](unsigned i) const {
    Assert(this->d_size > i);
    return this->d_arr[i];
  }
};/* CVC4::DynamicGrowingArray */

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__DYNAMIC_ARRAY_H */
