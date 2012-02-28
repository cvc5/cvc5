/*********************                                                        */
/*! \file cdqueue.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Context-dependent queue class
 **
 ** Context-dependent First-In-First-Out queue class.
 ** The implementation is based on a combination of CDList and a CDO<size_t>
 ** for tracking the next element to dequeue from the list.
 ** The implementation is currently very simple.
 **/


#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDQUEUE_H
#define __CVC4__CONTEXT__CDQUEUE_H

#include "context/context.h"
#include "context/cdlist.h"

namespace CVC4 {
namespace context {


template <class T>
class CDQueue {
private:

  /** List of elements in the queue. */
  CDList<T> d_list;

  /** Points to the next element in the current context to dequeue. */
  CDO<size_t> d_iter;


public:

  /** Creates a new CDQueue associated with the current context. */
  CDQueue(Context* context)
    : d_list(context),
      d_iter(context, 0)
  {}

  /** Returns true if the queue is empty in the current context. */
  bool empty() const{
    return d_iter >= d_list.size();
  }

  /** Enqueues an element in the current context. */
  void enqueue(const T& data){
    d_list.push_back(data);
  }

  /** Returns a reference to the next element on the queue. */
  const T& dequeue(){
    Assert(!empty(), "Attempting to queue from an empty queue.");
    size_t front = d_iter;
    d_iter = d_iter + 1;
    return d_list[front];
  }

};/* class CDQueue<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDQUEUE_H */
