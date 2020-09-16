/*********************                                                        */
/*! \file backtrackable.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Contains a backtrackable list
 **
 ** Contains a backtrackable list.
 **/

#include "cvc4_private.h"

#ifndef CVC4__UTIL__BACKTRACKABLE_H
#define CVC4__UTIL__BACKTRACKABLE_H

#include <cstdlib>
#include <vector>
#include "context/cdo.h"

namespace CVC4 {

template <class T> class List;
template <class T> class List_iterator;
template <class T> class Backtracker;

template <class T>
class ListNode {
private:
  T data;
  ListNode<T>* next;

  bool empty;
  ListNode(const T& t, ListNode<T>* n, bool e = false) : data(t), next(n), empty(e) {}
  ~ListNode() {
    // maybe set to NULL
    delete next;
  }

  friend class List<T>;
  friend class List_iterator<T>;
};/* class ListNode<T> */

template <class T>
class List_iterator : public std::iterator <std::forward_iterator_tag, T> {
  friend class List<T>;

public:
  const T& operator*();
  List_iterator<T>& operator++();
  List_iterator<T> operator++(int);
  bool operator!=(const List_iterator<T> & other) const;

private:
  const ListNode<T>* pointee;
  List_iterator(const ListNode<T>* p) : pointee(p) {}

};/* class List_iterator<T> */

template <class T>
const T& List_iterator<T>::operator*() {
  return pointee->data;
}

template <class T>
List_iterator<T>& List_iterator<T>::operator++() {
  Assert(pointee != NULL);
  pointee = pointee->next;
  while(pointee != NULL && pointee->empty ) {
    pointee = pointee->next;
  }
  return *this;
}

template <class T>
List_iterator<T> List_iterator<T>::operator++(int) {
  List_iterator<T> it = *this;
  ++*this;
  return it;
}

template <class T>
bool List_iterator<T>::operator!=(const List_iterator<T>& other) const {
  return (this->pointee != other.pointee);
}

// !! for the backtracking to work the lists must be allocated on the heap
// therefore the hashmap from TNode to List<TNode> should store pointers!
template <class T>
class List {
  ListNode<T>* head;
  ListNode<T>* tail;
  ListNode<T>* ptr_to_head;
  bool uninitialized;
  Backtracker<T>* bck;
  List (const List&) {}
public:
  List(Backtracker<T>* b) : ptr_to_head(NULL), uninitialized(true), bck(b) {
    head = tail = (ListNode<T>*)calloc(1,sizeof(ListNode<T>));
    head->next = NULL;
    head->empty = true;
  }
  ~List() {delete head;}
  bool empty() {
    bck->checkConsistency();
    return head == NULL;
  }
  void append(const T& d);
  //typedef List_iterator<T> iterator;
  typedef List_iterator<T> const_iterator;

  const_iterator begin() {
    bck->checkConsistency();
    if(head->empty) {
      ListNode<T>* temp = head;
      // if the head is empty return the first non-empty element or NULL
      while(temp != NULL && temp->empty ) {
        temp = temp->next;
      }
      return List_iterator<T>(temp);
    }
    return List_iterator<T>(head);
  }

  const_iterator end() {
    bck->checkConsistency();
    return List_iterator<T>(NULL);
  }
  void concat(List<T>* other);
  void unconcat(List<T>* other);
};/* class List */

template <class T>
void List<T>::append (const T& d) {
  bck->checkConsistency();

  if(uninitialized) {
    new(head)ListNode<T> (d, head->next);
    //head->data = d;
    head->empty = false;
    //Assert(tail == head); FIXME: do I need this because this list might be empty but append to another one
    uninitialized = false;

  } else {
    ListNode<T>* new_node = new ListNode<T>(d, head);
    head = new_node;
  }

  if(ptr_to_head != NULL) {
    ptr_to_head->next = head;
  }
}

template <class T>
void List<T>::concat (List<T>* other) {
  bck->checkConsistency();
  bck->notifyConcat(this, other);
  Assert(tail->next == NULL);
  tail->next = other->head;
  Assert(other->ptr_to_head == NULL);
  other->ptr_to_head = tail;
  tail = other->tail;
}

template <class T>
void List<T>::unconcat(List<T>* other) {
  // we do not need to check consistency since this is only called by the
  // Backtracker when we are inconsistent
  Assert(other->ptr_to_head != NULL);
  other->ptr_to_head->next = NULL;
  tail = other->ptr_to_head;
  other->ptr_to_head = NULL;
}

/* Backtrackable Table */

template <class T>
class Backtracker {
  friend class List<T>;
  std::vector<std::pair<List<T>*,List<T>*> > undo_stack;

  int curr_level;
  context::CDO<int> pop_level;

  void checkConsistency();
  void notifyConcat(List<T>* a, List<T>* b);
public:
  Backtracker(context::Context* c) : undo_stack(), curr_level(0), pop_level(c, 0) {}
  ~Backtracker() {}

};/* class Backtrackable */

template <class T>  void Backtracker<T>::notifyConcat(List<T>* a, List<T>* b) {
  curr_level++;
  pop_level.set(pop_level.get()+1);
  undo_stack.push_back( std::make_pair(a, b));
}

template <class T> void Backtracker<T>::checkConsistency() {
  if( curr_level == pop_level || pop_level == -1) {
    return;
  }
  Assert(curr_level > pop_level);

  while (curr_level > pop_level) {
    curr_level--;
    List<T>* l1 = undo_stack[curr_level].first;
    List<T>* l2 = undo_stack[curr_level].second;
    l1->unconcat(l2);
    undo_stack.pop_back();
  }
  Assert(curr_level == pop_level);
}

}/* CVC4 namespace */

#endif /* CVC4__UTIL__BACKTRACKABLE_H */
