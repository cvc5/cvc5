/*********************                                                        */
/*! \file channel.h
 ** \verbatim
 ** Original author: Morgan Deters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project but is excluded from the
 ** standard CVC4 licensing because it is a derivative work of
 ** circular_buffer.hpp in the BOOST 1.46.1 distribution.
 ** Thus this file is covered by the Boost Software License, version 1.0.
 ** See below.
 **
 ** The combined work is:
 **   Copyright (c) 2009-2014  New York University and The University of Iowa
 **   Copyright (c) 2003-2008  Jan Gaspar
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_public.h"

#ifndef __CVC4__CHANNEL_H
#define __CVC4__CHANNEL_H

#include <boost/circular_buffer.hpp>
#include <boost/thread/mutex.hpp>
#include <boost/thread/condition.hpp>
#include <boost/thread/thread.hpp>
#include <boost/call_traits.hpp>
#include <boost/progress.hpp>
#include <boost/bind.hpp>

namespace CVC4 {

template <typename T>
class CVC4_PUBLIC SharedChannel {
private:
  int d_maxsize;                // just call it size?
public:
  SharedChannel() {}
  SharedChannel(int maxsize) : d_maxsize(maxsize) {}
  virtual ~SharedChannel() {}

  /* Tries to add element and returns true if successful */
  virtual bool push(const T&) = 0;

  /* Removes an element from the channel */
  virtual T pop() = 0;

  /* */
  virtual bool empty() = 0;

  /* */
  virtual bool full() = 0;
};/* class SharedChannel<T> */

/*
This code is from

http://live.boost.org/doc/libs/1_46_1/libs/circular_buffer/doc/circular_buffer.html#boundedbuffer

and is covered by the Boost Software License, version 1.0.
*/
template <typename T>
class CVC4_PUBLIC SynchronizedSharedChannel : public SharedChannel<T> {
public:
  typedef boost::circular_buffer<T> container_type;
  typedef typename container_type::size_type size_type;
  typedef typename container_type::value_type value_type;
  typedef typename boost::call_traits<value_type>::param_type param_type;

  explicit SynchronizedSharedChannel(size_type capacity) : m_unread(0), m_container(capacity) {}

  bool push(param_type item){
  // param_type represents the "best" way to pass a parameter of type value_type to a method

    boost::mutex::scoped_lock lock(m_mutex);
    m_not_full.wait(lock, boost::bind(&SynchronizedSharedChannel<value_type>::is_not_full, this));
    m_container.push_front(item);
    ++m_unread;
    lock.unlock();
    m_not_empty.notify_one();
    return true;
  }//function definitions need to be moved to cpp

  value_type pop(){
    value_type ret;
    boost::mutex::scoped_lock lock(m_mutex);
    m_not_empty.wait(lock, boost::bind(&SynchronizedSharedChannel<value_type>::is_not_empty, this));
    ret = m_container[--m_unread];
    lock.unlock();
    m_not_full.notify_one();
    return ret;
  }


  bool empty() { return not is_not_empty(); }
  bool full() { return not is_not_full(); }

private:
  SynchronizedSharedChannel(const SynchronizedSharedChannel&);              // Disabled copy constructor
  SynchronizedSharedChannel& operator = (const SynchronizedSharedChannel&); // Disabled assign operator

  bool is_not_empty() const { return m_unread > 0; }
  bool is_not_full() const { return m_unread < m_container.capacity(); }

  size_type m_unread;
  container_type m_container;
  boost::mutex m_mutex;
  boost::condition m_not_empty;
  boost::condition m_not_full;
};/* class SynchronizedSharedChannel<T> */

}/* CVC4 namespace */

#endif /* __CVC4__CHANNEL_H */
