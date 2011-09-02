/*********************                                                        */
/*! \file cdcirclist.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Context-dependent circular list class
 **
 ** Context-dependent circular list class.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDCIRCLIST_H
#define __CVC4__CONTEXT__CDCIRCLIST_H

#include <iterator>
#include <memory>
#include <string>
#include <sstream>

#include "context/context.h"
#include "context/context_mm.h"
#include "context/cdcirclist_forward.h"
#include "context/cdo.h"
#include "util/Assert.h"

namespace CVC4 {
namespace context {

// CDO for pointers in particular, adds * and -> operators
template <class T>
class CDPtr : public CDO<T*> {
  typedef CDO<T*> super;

  // private copy ctor
  CDPtr(const CDPtr<T>& cdptr) :
    super(cdptr) {
  }

public:

  CDPtr(Context* context, T* data = NULL) :
    super(context, data) {
  }

  CDPtr(bool allocatedInCMM, Context* context, T* data = NULL) :
    super(allocatedInCMM, context, data) {
  }

  // undesirable to put this here, since CDO<> does it already (?)
  virtual ~CDPtr() throw(AssertionException) { this->destroy(); }

  virtual ContextObj* save(ContextMemoryManager* pCMM) {
    Debug("context") << "save cdptr " << this << " (value " << super::get() << ")";
    ContextObj* p = new(pCMM) CDPtr<T>(*this);
    Debug("context") << " to " << p << std::endl;
    return p;
  }

  virtual void restore(ContextObj* pContextObj) {
    Debug("context") << "restore cdptr " << this << " (using " << pContextObj << ") from " << super::get();
    this->super::restore(pContextObj);
    Debug("context") << " to " << super::get() << std::endl;
  }

  CDPtr<T>& operator=(T* data) {
    Debug("context") << "set " << this << " from " << super::get();
    super::set(data);
    Debug("context") << " to " << super::get() << std::endl;
    return *this;
  }
  // assignment is just like using the underlying ptr
  CDPtr<T>& operator=(const CDPtr<T>& cdptr) {
    return *this = cdptr.get();
  }

  T& operator*() { return *super::get(); }
  T* operator->() { return super::get(); }
  const T& operator*() const { return *super::get(); }
  const T* operator->() const { return super::get(); }
};/* class CDPtr<T> */


/**
 * Class representing a single link in a CDCircList<>.
 *
 * The underlying T object is immutable, only the structure of the
 * list is mutable, so only that's backtracked.
 */
template <class T, class AllocatorT>
class CDCircElement {
  typedef CDCircElement<T, AllocatorT> elt_t;
  const T d_t;
  CDPtr<elt_t> d_prev;
  CDPtr<elt_t> d_next;
  friend class CDCircList<T, AllocatorT>;
public:
  CDCircElement(Context* context, const T& t,
                elt_t* prev = NULL, elt_t* next = NULL) :
    d_t(t),
    d_prev(true, context, prev),
    d_next(true, context, next) {
  }

  CDPtr<elt_t>& next() { return d_next; }
  CDPtr<elt_t>& prev() { return d_prev; }
  elt_t* next() const { return d_next; }
  elt_t* prev() const { return d_prev; }
  T element() const { return d_t; }
};/* class CDCircElement<> */


/**
 * Generic context-dependent circular list.  Items themselves are not
 * context dependent, only the forward and backward links.  This
 * allows two lists to be spliced together in constant time (see
 * concat()).  The list *structure* is mutable (things can be spliced
 * in, removed, added, the list can be cleared, etc.) in a
 * context-dependent manner, but the list items are immutable.  To
 * replace an item A in the list with B, A must be removed and
 * B added in the same location.
 */
template <class T, class AllocatorT>
class CDCircList : public ContextObj {
public:

  /** List carrier element type */
  typedef CDCircElement<T, AllocatorT> elt_t;
  /** The value type with which this CDCircList<> was instantiated. */
  typedef T value_type;
  /** The allocator type with which this CDCircList<> was instantiated. */
  typedef AllocatorT Allocator;

private:

  /** Head element of the circular list */
  CDPtr<elt_t> d_head;
  /** The context with which we're associated */
  Context* d_context;
  /** Our allocator */
  typename Allocator::template rebind< CDCircElement<T, AllocatorT> >::other d_allocator;

public:

  CDCircList(Context* context, const Allocator& alloc = Allocator()) :
    ContextObj(context),
    d_head(context, NULL),
    d_context(context),
    d_allocator(alloc) {
  }

  CDCircList(bool allocatedInCMM, Context* context, const Allocator& alloc = Allocator()) :
    ContextObj(allocatedInCMM, context),
    d_head(allocatedInCMM, context, NULL),
    d_context(context),
    d_allocator(alloc) {
    Debug("cdcirclist") << "head " << &d_head << " in cmm ? " << allocatedInCMM << std::endl;
  }

  ~CDCircList() throw(AssertionException) {
    // by context contract, call destroy() here
    destroy();
  }

  void clear() {
    d_head = NULL;
  }

  bool empty() const {
    return d_head == NULL;
  }

  CDPtr<elt_t>& head() {
    return d_head;
  }

  CDPtr<elt_t>& tail() {
    return empty() ? d_head : d_head->d_prev;
  }

  const elt_t* head() const {
    return d_head;
  }

  const elt_t* tail() const {
    return empty() ? d_head : d_head->d_prev;
  }

  T front() const {
    Assert(! empty());
    return head()->element();
  }

  T back() const {
    Assert(! empty());
    return tail()->element();
  }

  void push_back(const T& t) {
    if(Debug.isOn("cdcirclist:paranoid")) {
      debugCheck();
    }
    // FIXME LEAK! (should alloc in CMM, no?)
    elt_t* x = d_allocator.allocate(1);
    if(empty()) {
      // zero-element case
      new(x) elt_t(d_context, t, x, x);
      d_head = x;
    } else {
      // N-element case
      new(x) elt_t(d_context, t, d_head->d_prev, d_head);
      d_head->d_prev->d_next = x;
      d_head->d_prev = x;
    }
  }

  /**
   * Concatenate two lists.  This modifies both: afterward, the two
   * lists might have different heads, but they will have the same
   * elements in the same (circular) order.
   */
  void concat(CDCircList<T, AllocatorT>& l) {
    Assert(this != &l, "cannot concat a list with itself");

    if(d_head == NULL) {
      d_head = l.d_head;
      return;
    } else if(l.d_head == NULL) {
      l.d_head = d_head;
      return;
    }

    // splice together the two circular lists
    CDPtr<elt_t> &l1head = head(), &l2head = l.head();
    CDPtr<elt_t> &l1tail = tail(), &l2tail = l.tail();
    // l2tail will change underneath us in what's below (because it's
    // the same as l2head->prev()), so we have to keep a regular
    // pointer to it
    elt_t* oldl2tail = l2tail;

    Debug("cdcirclist") << "concat1 " << this << " " << &l << std::endl;
    l1tail->next() = l2head;
    Debug("cdcirclist") << "concat2" << std::endl;
    l2head->prev() = l1tail;

    Debug("cdcirclist") << "concat3" << std::endl;
    oldl2tail->next() = l1head;
    Debug("cdcirclist") << "concat4" << std::endl;
    l1head->prev() = oldl2tail;
    Debug("cdcirclist") << "concat5" << std::endl;
  }

  class iterator {
    const CDCircList<T, AllocatorT>* d_list;
    const elt_t* d_current;
    friend class CDCircList<T, AllocatorT>;
  public:
    iterator(const CDCircList<T, AllocatorT>* list, const elt_t* first) :
      d_list(list),
      d_current(first) {
    }
    iterator(const iterator& other) :
      d_list(other.d_list),
      d_current(other.d_current) {
    }

    bool operator==(const iterator& other) const {
      return d_list == other.d_list && d_current == other.d_current;
    }
    bool operator!=(const iterator& other) const {
      return !(*this == other);
    }
    iterator& operator++() {
      Assert(d_current != NULL, "iterator already off the end");
      if(d_current == d_list->tail()) {
        d_current = NULL;
      } else {
        d_current = d_current->next();
      }
      return *this;
    }
    iterator operator++(int) {
      const elt_t* old = d_current;
      ++*this;
      return iterator(d_list, old);
    }
    iterator& operator--() {
      // undefined to go off the beginning, but don't have a check for that
      if(d_current == NULL) {
        d_current = d_list->tail();
      } else {
        d_current = d_current->prev();
      }
      return *this;
    }
    iterator operator--(int) {
      const elt_t* old = d_current;
      --*this;
      return iterator(d_list, old);
    }
    T operator*() {
      Assert(d_current != NULL, "iterator already off the end");
      return d_current->element();
    }
  };/* class CDCircList<>::iterator */

  // list elements are immutable
  typedef iterator const_iterator;

  iterator begin() {
    if(Debug.isOn("cdcirclist:paranoid")) {
      debugCheck();
    }
    return iterator(this, head());
  }

  iterator end() {
    if(Debug.isOn("cdcirclist:paranoid")) {
      debugCheck();
    }
    return iterator(this, NULL);
  }

  const_iterator begin() const {
    return const_iterator(this, head());
  }

  const_iterator end() const {
    return const_iterator(this, NULL);
  }

  iterator erase(iterator pos) {
    Assert(pos.d_current != NULL);
    if(pos.d_current->prev() == pos.d_current) {
      // one-elt list
      d_head = NULL;
      return iterator(this, NULL);
    } else {
      // N-elt list
      if(pos.d_current == d_head) {
        // removing list head
        elt_t *pHead = head(), *pTail = tail();
        pTail->next() = pHead->next();
        pHead->next()->prev() = pTail;
        d_head = pHead->next();
        return iterator(this, d_head);
        // can't free old head, because of backtracking
      } else {
        // not removing list head
        const elt_t *elt = pos.d_current;
        elt_t *prev = pos.d_current->prev();
        prev->next() = elt->next();
        elt->next()->prev() = prev;
        return iterator(this, elt->next());
        // can't free elt, because of backtracking
      }
    }
  }

private:

  // do not permit copy/assignment
  CDCircList(const CDCircList<T, AllocatorT>&) CVC4_UNUSED;
  CDCircList<T, AllocatorT>& operator=(const CDCircList<T, AllocatorT>&) CVC4_UNUSED;

public:
  /** Check internal structure and invariants of the list */
  void debugCheck() const {
    elt_t* p = d_head;
    Debug("cdcirclist") << "this is " << this << std::endl;
    if(p == NULL) {
      Debug("cdcirclist") << "head[" << &d_head << "] is NULL : " << d_context->getLevel() << std::endl;
      // empty list
      return;
    }
    Debug("cdcirclist") << "head[" << &d_head << "] is " << p << " next " << p->d_next << " prev " << p->d_prev << " : " << d_context->getLevel() << std::endl;//p->d_t << std::endl;
    do {
      elt_t* p_last = p;
      p = p->d_next;
      if(p == NULL) {
        Debug("cdcirclist") << "****** ERROR ON LINE ABOVE, next == NULL ******" << std::endl;
        break;
      }
      Debug("cdcirclist") << "   p is " << p << " next " << p->d_next << " prev " << p->d_prev << " : " << std::endl;//p->d_t << std::endl;
      if(p->d_prev != p_last) {
        Debug("cdcirclist") << "****** ERROR ON LINE ABOVE, prev != last ******" << std::endl;
      }
      //Assert(p->d_prev == p_last);
      Assert(p != NULL);
    } while(p != d_head);
  }

private:

  // Nothing to save; the elements take care of themselves
  virtual ContextObj* save(ContextMemoryManager* pCMM) {
    Unreachable();
  }

  // Similarly, nothing to restore
  virtual void restore(ContextObj* data) {
    Unreachable();
  }

};/* class CDCircList<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDCIRCLIST_H */
