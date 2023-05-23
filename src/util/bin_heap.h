/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Morgan Deters, Yancheng Ou
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * An implementation of a binary heap
 *
 * Attempts to roughly follow the contract of Boost's d_ary_heap.
 * (http://www.boost.org/doc/libs/1_49_0/doc/html/boost/heap/d_ary_heap.html)
 * Also attempts to generalize ext/pd_bs/priority_queue.
 * (http://gcc.gnu.org/onlinedocs/libstdc++/ext/pb_ds/priority_queue.html)
 */

#include "cvc5_private.h"

#ifndef CVC5__BIN_HEAP_H
#define CVC5__BIN_HEAP_H

#include <limits>
#include <functional>

#include "base/check.h"
#include "base/exception.h"

namespace cvc5::internal {

/**
 * BinaryHeap that orders its elements greatest-first (i.e., in the opposite
 * direction of the provided comparator).  Update of elements is permitted
 * via handles, which are not invalidated by mutation (pushes and pops etc.).
 * Handles are invalidted when their element is no longer a member of the
 * heap.  Iteration over elements is supported but iteration is unsorted and
 * iterators are immutable.
 */
template <class Elem, class CmpFcn = std::less<Elem> >
class BinaryHeap {
private:
  typedef Elem T;
  struct HElement;

  typedef std::vector<HElement*> ElementVector;

  struct HElement {
    HElement(size_t pos, const T& elem): d_pos(pos), d_elem(elem) {}
    size_t d_pos;
    T d_elem;
  };/* struct HElement */

  /** A 0 indexed binary heap. */
  ElementVector d_heap;

  /** The comparator. */
  CmpFcn d_cmp;

  // disallow copy and assignment
  BinaryHeap(const BinaryHeap&) = delete;
  BinaryHeap& operator=(const BinaryHeap&) = delete;

public:
  BinaryHeap(const CmpFcn& c = CmpFcn())
    : d_heap()
    , d_cmp(c)
  {}

  ~BinaryHeap(){
    clear();
  }

  class handle {
  private:
    HElement* d_pointer;
    handle(HElement* p) : d_pointer(p){}
    friend class BinaryHeap;
  public:
    handle() : d_pointer(NULL) {}
    const T& operator*() const {
      Assert(d_pointer != NULL);
      return d_pointer->d_elem;
    }

    bool operator==(const handle& h) const {
      return d_pointer == h.d_pointer;
    }

    bool operator!=(const handle& h) const {
      return d_pointer != h.d_pointer;
    }

  }; /* BinaryHeap<>::handle */

  class const_iterator {
  public:
    /* The following types are required by trait std::iterator_traits */

    /** Iterator tag */
    using iterator_category = std::forward_iterator_tag;

    /** The type of the item */
    using value_type = Elem;

    /** The pointer type of the item */
    using pointer = const Elem*;

    /** The reference type of the item */
    using reference = const Elem&;

    /** The type returned when two iterators are subtracted */
    using difference_type = std::ptrdiff_t;

    /* End of std::iterator_traits required types */

  private:
    typename ElementVector::const_iterator d_iter;
    friend class BinaryHeap;
    const_iterator(const typename ElementVector::const_iterator& iter)
      : d_iter(iter)
    {}
  public:
    const_iterator(){}
    inline bool operator==(const const_iterator& ci) const{
      return d_iter == ci.d_iter;
    }
    inline bool operator!=(const const_iterator& ci) const{
      return d_iter != ci.d_iter;
    }
    inline const_iterator& operator++(){
      ++d_iter;
      return *this;
    }
    inline const_iterator operator++(int){
      const_iterator i = *this;
      ++d_iter;
      return i;
    }
    inline const T& operator*() const{
      const HElement* he = *d_iter;
      return he->d_elem;
    }

  };/* BinaryHeap<>::const_iterator */

  typedef const_iterator iterator;

  inline size_t size() const { return d_heap.size(); }
  inline bool empty() const { return d_heap.empty(); }

  inline const_iterator begin() const {
    return const_iterator(d_heap.begin());
  }

  inline const_iterator end() const {
    return const_iterator(d_heap.end());
  }

  void clear(){
    typename ElementVector::iterator i=d_heap.begin(), iend=d_heap.end();
    for(; i!=iend; ++i){
      HElement* he = *i;
      delete he;
    }
    d_heap.clear();
  }

  void swap(BinaryHeap& heap){
    std::swap(d_heap, heap.d_heap);
    std::swap(d_cmp, heap.d_cmp);
  }

  handle push(const T& toAdded){
    Assert(size() < MAX_SIZE);
    HElement* he = new HElement(size(), toAdded);
    d_heap.push_back(he);
    up_heap(he);
    return handle(he);
  }

  void erase(handle h){
    Assert(!empty());
    Assert(debugHandle(h));

    HElement* he = h.d_pointer;
    size_t pos = he->d_pos;
    if(pos == root()){
      // the top element can be efficiently removed by pop
      pop();
    }else if(pos == last()){
      // the last element can be safely removed
      d_heap.pop_back();
      delete he;
    }else{
      // This corresponds to
      // 1) swapping the elements at pos with the element at last:
      // 2) deleting the new last element
      // 3) updating the position of the new element at pos
      swapIndices(pos, last());
      d_heap.pop_back();
      delete he;
      update(handle(d_heap[pos]));
    }
  }

  void pop(){
    Assert(!empty());
    swapIndices(root(), last());
    HElement* b = d_heap.back();
    d_heap.pop_back();
    delete b;

    if(!empty()){
      down_heap(d_heap.front());
    }
  }

  const T& top() const {
    Assert(!empty());
    return (d_heap.front())->d_elem;
  }

private:
  void update(handle h){
    Assert(!empty());
    Assert(debugHandle(h));

    // The relationship between h and its parent, left and right has become unknown.
    // But it is assumed that parent <= left, and parent <= right still hold.
    // Figure out whether to up_heap or down_heap.

    Assert(!empty());
    HElement* he = h.d_pointer;

    size_t pos = he->d_pos;
    if(pos == root()){
      // no parent
      down_heap(he);
    }else{
      size_t par = parent(pos);
      HElement* at_parent = d_heap[par];
      if(gt(he->d_elem, at_parent->d_elem)){
        // he > parent
        up_heap(he);
      }else{
        down_heap(he);
      }
    }
  }

public:
  void update(handle h, const T& val){
    Assert(!empty());
    Assert(debugHandle(h));
    h.d_pointer->d_elem = val;
    update(h);
  }

  /** (std::numeric_limits<size_t>::max()-2)/2; */
  static const size_t MAX_SIZE;

private:
  inline bool gt(const T& a, const T& b) const{
    // cmp acts like an operator<
    return d_cmp(b, a);
  }

  inline bool lt(const T& a, const T& b) const{
    return d_cmp(a, b);
  }

  inline static size_t parent(size_t p){
    Assert(p != root());
    return (p-1)/2;
  }
  inline static size_t right(size_t p){ return 2*p+2; }
  inline static size_t left(size_t p){ return 2*p+1; }
  inline static size_t root(){ return 0; }
  inline size_t last() const{
    Assert(!empty());
    return size() - 1;
  }

  inline void swapIndices(size_t i, size_t j){
    HElement* at_i = d_heap[i];
    HElement* at_j = d_heap[j];
    swap(i,j,at_i,at_j);
  }

  inline void swapPointers(HElement* at_i, HElement* at_j){
    // still works if at_i == at_j
    size_t i = at_i->d_pos;
    size_t j = at_j->d_pos;
    swap(i,j,at_i,at_j);
  }

  inline void swap(size_t i, size_t j, HElement* at_i, HElement* at_j){
    // still works if i == j
    Assert(i == at_i->d_pos);
    Assert(j == at_j->d_pos);
    d_heap[i] = at_j;
    d_heap[j] = at_i;
    at_i->d_pos = j;
    at_j->d_pos = i;
  }

  void up_heap(HElement* he){
    const size_t& curr = he->d_pos;
    // The value of curr changes implicitly during swap operations.
    while(curr != root()){
      // he->d_elem > parent
      size_t par = parent(curr);
      HElement* at_parent = d_heap[par];
      if(gt(he->d_elem, at_parent->d_elem)){
        swap(curr, par, he, at_parent);
      }else{
        break;
      }
    }
  }

  void down_heap(HElement* he){
    const size_t& curr = he->d_pos;
    // The value of curr changes implicitly during swap operations.
    size_t N = size();
    size_t r, l;

    while((r = right(curr)) < N){
      l = left(curr);

      // if at_left == at_right, favor left
      HElement* at_left = d_heap[l];
      HElement* at_right = d_heap[r];
      if(lt(he->d_elem, at_left->d_elem)){
        // he < at_left
        if(lt(at_left->d_elem, at_right->d_elem)){
          // he < at_left < at_right
          swap(curr, r, he, at_right);
        }else{
          //       he <  at_left
          // at_right <= at_left
          swap(curr, l, he, at_left);
        }
      }else{
        // at_left <= he
        if(lt(he->d_elem, at_right->d_elem)){
          // at_left <= he < at_right
          swap(curr, r, he, at_right);
        }else{
          // at_left  <= he
          // at_right <= he
          break;
        }
      }
    }
    l = left(curr);
    if(r >= N && l < N){
      // there is a left but not a right
      HElement* at_left = d_heap[l];
      if(lt(he->d_elem, at_left->d_elem)){
        // he < at_left
        swap(curr, l, he, at_left);
      }
    }
  }

  bool debugHandle(handle h) const{
    HElement* he = h.d_pointer;
    if( he == NULL ){
      return true;
    }else if(he->d_pos >= size()){
      return false;
    }else{
      return he == d_heap[he->d_pos];
    }
  }

}; /* class BinaryHeap<> */

template <class Elem, class CmpFcn>
const size_t BinaryHeap<Elem,CmpFcn>::MAX_SIZE = (std::numeric_limits<size_t>::max()-2)/2;

}  // namespace cvc5::internal

#endif /* CVC5__BIN_HEAP_H */
