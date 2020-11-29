/*********************                                                        */
/*! \file cdqueue.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Francois Bobot, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Context-dependent queue class
 **
 ** Context-dependent First-In-First-Out queue class.
 ** This implementation may discard elements which are enqueued and dequeued
 ** at the same context level.
 **
 ** The implementation is based on a CDList with one additional size_t
 ** for tracking the next element to dequeue from the list and additional
 ** size_t for tracking the previous size of the list.
 **/


#include "cvc4_private.h"

#ifndef CVC4__CONTEXT__CDQUEUE_H
#define CVC4__CONTEXT__CDQUEUE_H

#include "context/context.h"
#include "context/cdlist.h"

namespace CVC4 {
namespace context {

template <class T, class CleanUp = DefaultCleanUp<T>, class Allocator = std::allocator<T> >
class CDQueue;

/** We don't define a template with Allocator for the first implementation */
template <class T, class CleanUp, class Allocator>
class CDQueue : public CDList<T, CleanUp, Allocator> {
private:
  typedef CDList<T, CleanUp, Allocator> ParentType;

protected:

  /** Points to the next element in the current context to dequeue. */
  size_t d_iter;

  /** Points to the size at the last save. */
  size_t d_lastsave;

  /**
   * Private copy constructor used only by save().
   */
  CDQueue(const CDQueue<T, CleanUp, Allocator>& l):
    ParentType(l),
    d_iter(l.d_iter),
    d_lastsave(l.d_lastsave) {}

  /** Implementation of mandatory ContextObj method save:
   *  We assume that the base class do the job inside their copy constructor.
   */
  ContextObj* save(ContextMemoryManager* pCMM) override
  {
    ContextObj* data = new(pCMM) CDQueue<T, CleanUp, Allocator>(*this);
    // We save the d_size in d_lastsave and we should never destruct below this
    // indices before the corresponding restore.
    d_lastsave = ParentType::d_size;
    Debug("cdqueue") << "save " << this
                     << " at level " << this->getContext()->getLevel()
                     << " size at " << this->d_size
                     << " iter at " << this->d_iter
                     << " lastsave at " << this->d_lastsave
                     << " d_list is " << this->d_list
                     << " data:" << data << std::endl;
    return data;
  }

  /**
   * Implementation of mandatory ContextObj method restore: simply
   * restores the previous size, iter and lastsave indices. Note that
   * the list pointer and the allocated size are not changed.
   */
  void restore(ContextObj* data) override
  {
    CDQueue<T, CleanUp, Allocator>* qdata = static_cast<CDQueue<T, CleanUp, Allocator>*>(data);
    d_iter = qdata->d_iter;
    d_lastsave = qdata->d_lastsave;
    ParentType::restore(data);
  }



public:

  /** Creates a new CDQueue associated with the current context. */
  CDQueue(Context* context,
          bool callDestructor = true,
          const CleanUp& cleanup = CleanUp(),
          const Allocator& alloc = Allocator())
    : ParentType(context, callDestructor, cleanup, alloc),
      d_iter(0),
      d_lastsave(0)
  {}

  /** Returns true if the queue is empty in the current context. */
  bool empty() const{
    Assert(d_iter <= ParentType::d_size);
    return d_iter == ParentType::d_size;
  }

  /** Returns the number of elements that have not been dequeued in the context. */
  size_t size() const{
    return ParentType::d_size - d_iter;
  }

  /** Enqueues an element in the current context. */
  void push(const T& data){
    ParentType::push_back(data);
  }

  /**
   * Delete next element. The destructor of this object will be
   * called eventually but not necessarily during the call of this
   * function.
   */
  void pop(){
    Assert(!empty()) << "Attempting to pop from an empty queue.";
    ParentType::makeCurrent();
    d_iter = d_iter + 1;
    if (empty() && d_lastsave != ParentType::d_size) {
      // Some elements have been enqueued and dequeued in the same
      // context and now the queue is empty we can destruct them.
      ParentType::truncateList(d_lastsave);
      Assert(ParentType::d_size == d_lastsave);
      d_iter = d_lastsave;
    }
  }

  /** Returns a reference to the next element on the queue. */
  const T& front() const{
    Assert(!empty()) << "No front in an empty queue.";
    return ParentType::d_list[d_iter];
  }

  /**
   * Returns the most recent item added to the queue.
   */
  const T& back() const {
    Assert(!empty()) << "CDQueue::back() called on empty list";
    return ParentType::d_list[ParentType::d_size - 1];
  }

  typedef typename ParentType::const_iterator const_iterator;

  const_iterator begin() const {
    return ParentType::begin() + d_iter;
  }

  const_iterator end() const {
    return ParentType::end();
  }

};/* class CDQueue<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* CVC4__CONTEXT__CDQUEUE_H */
