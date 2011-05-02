/*********************                                                        */
/*! \file dynamic_array.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/


#include "cvc4_private.h"

#ifndef __CVC4__UTIL__DYNAMICARRAY_H
#define __CVC4__UTIL__DYNAMICARRAY_H

#include "util/Assert.h"

namespace CVC4 {

template <class T>
class DynamicArray {
private:
  T* d_arr;
  unsigned d_size;
  unsigned d_allocated;

  bool d_callDestructor;

  void grow(){
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
  DynamicArray(bool deallocate = false):
    d_arr(NULL),
    d_size(0),
    d_allocated(0),
    d_callDestructor(deallocate){
  }

  ~DynamicArray(){
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

  T& operator[](unsigned i) {
    Assert(i < d_size, "index out of bounds in DynamicArray::operator[]");
    return d_arr[i];
  }

  const T& back() const{
    Assert(d_size > 0, "DynamicArray::back() called on empty list");
    return d_arr[d_size - 1];
  }

  void pop_back() {
    Assert(d_size > 0, "DynamicArray::back() called on empty list");
    --d_size;
    if(d_callDestructor){
      d_arr[d_size].~T();;
    }
  }
};/* CVC4::DynamicArray */

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__DYNAMICARRAY_H */
