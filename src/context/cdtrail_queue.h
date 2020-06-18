/*********************                                                        */
/*! \file cdtrail_queue.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Context-dependent queue class with an explicit trail of elements
 **
 ** Context-dependent First-In-First-Out queue class.
 ** The implementation is based on a combination of CDList and a CDO<size_t>
 ** for tracking the next element to dequeue from the list.
 ** The implementation is currently not full featured.
 **/


#include "cvc4_private.h"

#ifndef CVC4__CONTEXT__CDTRAIL_QUEUE_H
#define CVC4__CONTEXT__CDTRAIL_QUEUE_H

#include "context/context.h"
#include "context/cdlist.h"

namespace CVC4 {
namespace context {


template <class T>
class CDTrailQueue {
private:

  /** List of elements in the queue. */
  CDList<T> d_list;

  /** Points to the next element in the current context to dequeue. */
  CDO<size_t> d_iter;


public:

  /** Creates a new CDTrailQueue associated with the current context. */
  CDTrailQueue(Context* context)
    : d_list(context),
      d_iter(context, 0)
  {}

  /** Returns true if the queue is empty in the current context. */
  bool empty() const{
    return d_iter >= d_list.size();
  }

  /**
   * Enqueues an element in the current context.
   * Returns its index in the queue.
   */
  size_t enqueue(const T& data){
    size_t res = d_list.size();
    d_list.push_back(data);
    return res;
  }

  size_t frontIndex() const{
    return d_iter;
  }

  const T& front() const{
    return d_list[frontIndex()];
  }

  /** Moves the iterator for the queue forward. */
  void dequeue(){
    Assert(!empty()) << "Attempting to queue from an empty queue.";
    d_iter = d_iter + 1;
  }

  const T& operator[](size_t index) const{
    Assert(index < d_list.size());
    return d_list[index];
  }

  size_t size() const{
    return d_list.size();
  }

};/* class CDTrailQueue<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* CVC4__CONTEXT__CDTRAIL_QUEUE_H */
