/*********************                                                        */
/*! \file cdlist.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Context-dependent list class (only supports append)
 **
 ** Context-dependent list class.  This list only supports appending
 ** to the list; on backtrack, the list is simply shortened.
 **/

#include "cvc4_private.h"

#ifndef CVC4__CONTEXT__CDLIST_H
#define CVC4__CONTEXT__CDLIST_H

#include <iterator>
#include <memory>
#include <sstream>
#include <string>
#include <vector>

#include "base/check.h"
#include "context/cdlist_forward.h"
#include "context/context.h"
#include "context/context_mm.h"
#include "context/default_clean_up.h"

namespace CVC4 {
namespace context {

/**
 * Generic context-dependent dynamic array.  Note that for efficiency, this
 * implementation makes the following assumption: Over time, objects are only
 * added to the list.  Objects are only removed when a pop restores the list to
 * a previous state.
 */
template <class T, class CleanUpT, class Allocator>
class CDList : public ContextObj
{
 public:
  /** The value type with which this CDList<> was instantiated. */
  using value_type = T;

  /** The cleanup type with which this CDList<> was instantiated. */
  using CleanUp = CleanUpT;

  /**
   * `std::vector<T>::operator[] const` returns an
   * std::vector<T>::const_reference, which does not necessarily have to be a
   * `const T&`. Specifically, in the case of `std::vector<bool>`, the type is
   * specialized to be just a simple `bool`. For our `operator[] const`, we use
   * the same type.
   */
  using ConstReference = typename std::vector<T>::const_reference;

  /**
   * Main constructor: d_list starts with size 0
   *
   * Optionally, a cleanup callback can be specified, which is called on every
   * element that gets removed during a pop. The callback is only used when
   * callCleanup is true. Note: the destructor of the elements in the list is
   * called regardless of whether callCleanup is true or false.
   */
  CDList(Context* context,
         bool callCleanup = true,
         const CleanUp& cleanup = CleanUp())
      : ContextObj(context),
        d_list(),
        d_size(0),
        d_callCleanup(callCleanup),
        d_cleanUp(cleanup)
  {
  }

  /**
   * Destructor: delete the list
   */
  ~CDList() {
    this->destroy();

    if (this->d_callCleanup)
    {
      truncateList(0);
    }
  }

  /**
   * Return the current size of (i.e. valid number of objects in) the
   * list.
   */
  size_t size() const { return d_list.size(); }

  /**
   * Return true iff there are no valid objects in the list.
   */
  bool empty() const { return d_list.empty(); }

  /**
   * Add an item to the end of the list.
   */
  void push_back(const T& data) {
    Debug("cdlist") << "push_back " << this << " " << getContext()->getLevel()
                    << ": make-current" << std::endl;
    makeCurrent();

    d_list.push_back(data);
    ++d_size;

    Debug("cdlist") << "push_back " << this
                    << " " << getContext()->getLevel()
                    << ": size now " << d_size << std::endl;
  }

  /**
   * Access to the ith item in the list.
   */
  ConstReference operator[](size_t i) const
  {
    Assert(i < d_size) << "index out of bounds in CDList::operator[]";
    return d_list[i];
  }

  /**
   * Returns the most recent item added to the list.
   */
  ConstReference back() const
  {
    Assert(d_size > 0) << "CDList::back() called on empty list";
    return d_list[d_size - 1];
  }

  /**
   * Iterator for CDList class.  It has to be const because we don't
   * allow items in the list to be changed.  It's a straightforward
   * wrapper around a pointer.  Note that for efficiency, we implement
   * only prefix increment and decrement.  Also note that it's OK to
   * create an iterator from an empty, uninitialized list, as begin()
   * and end() will have the same value (NULL).
   */
  class const_iterator {
   public:
    typedef std::input_iterator_tag iterator_category;
    typedef T value_type;
    typedef std::ptrdiff_t difference_type;
    typedef const T* pointer;
    typedef const T& reference;

    const_iterator() : d_list(nullptr), d_pos(-1) {}
    const_iterator(const std::vector<T>* list, size_t pos)
        : d_list(list), d_pos(pos)
    {
    }

    bool operator==(const const_iterator& other) const
    {
      return d_list == other.d_list && d_pos == other.d_pos;
    }

    bool operator!=(const const_iterator& other) const
    {
      return d_list != other.d_list || d_pos != other.d_pos;
    }

    const T& operator*() const { return (*d_list)[d_pos]; }
    const T* operator->() const { return &(*d_list)[d_pos]; }

    /** Prefix increment */
    const_iterator& operator++() {
      ++d_pos;
      return *this;
    }

    /** Prefix decrement */
    const_iterator& operator--()
    {
      --d_pos;
      return *this;
    }

    /** operator+ */
    const_iterator operator+(long signed int off) const {
      return const_iterator(d_list, d_pos + off);
    }

   private:
    const std::vector<T>* d_list;
    size_t d_pos;
  }; /* class CDList<>::const_iterator */
  typedef const_iterator iterator;

  /**
   * Returns an iterator pointing to the first item in the list.
   */
  const_iterator begin() const { return const_iterator(&d_list, 0); }

  /**
   * Returns an iterator pointing one past the last item in the list.
   */
  const_iterator end() const { return const_iterator(&d_list, d_size); }

 protected:
  /**
   * Private copy constructor used only by save(). d_list is not copied: only
   * the base class information and d_size are needed in restore.
   */
  CDList(const CDList& l)
      : ContextObj(l),
        d_size(l.d_size),
        d_callCleanup(false),
        d_cleanUp(l.d_cleanUp)
  {
    Debug("cdlist") << "copy ctor: " << this << " from " << &l << " size "
                    << d_size << std::endl;
  }
  CDList& operator=(const CDList& l) = delete;
  /**
   * Implementation of mandatory ContextObj method restore: simply
   * restores the previous size.  Note that the list pointer and the
   * allocated size are not changed.
   */

  void restore(ContextObj* data) override
  {
    Debug("cdlist") << "restore " << this << " level "
                    << this->getContext()->getLevel() << " data == " << data
                    << " call dtor == " << this->d_callCleanup << std::endl;
    truncateList(((CDList<T, CleanUp, Allocator>*)data)->d_size);
    Debug("cdlist") << "restore " << this << " level "
                    << this->getContext()->getLevel() << " size back to "
                    << this->d_size << std::endl;
  }

  /**
   * Given a size parameter smaller than d_size, truncateList()
   * removes the elements from the end of the list until d_size equals size.
   *
   * WARNING! You should only use this function when you know what you are
   * doing. This is a primitive operation with strange context dependent
   * behavior! It is up to the user of the function to ensure that the saved
   * d_size values at lower context levels are less than or equal to size.
   */
  void truncateList(const size_t size)
  {
    Assert(size <= d_size);
    if (d_callCleanup)
    {
      while (d_size != size)
      {
        --d_size;
        typename std::vector<T>::reference elem = d_list[d_size];
        d_cleanUp(elem);
      }
    }
    else
    {
      d_size = size;
    }
    d_list.erase(d_list.begin() + d_size, d_list.end());
  }

  /**
   * d_list is a vector of objects of type T.
   */
  std::vector<T> d_list;

  /**
   * Number of objects in d_list
   */
  size_t d_size;

 private:
  /**
   * Whether to call the destructor when items are popped from the
   * list.  True by default, but can be set to false by setting the
   * second argument in the constructor to false.
   */
  bool d_callCleanup;

  /**
   * The CleanUp functor.
   */
  CleanUp d_cleanUp;

  /**
   * Implementation of mandatory ContextObj method save: simply copies
   * the current size to a copy using the copy constructor (the
   * pointer and the allocated size are *not* copied as they are not
   * restored on a pop).  The saved information is allocated using the
   * ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) override
  {
    ContextObj* data = new (pCMM) CDList<T, CleanUp, Allocator>(*this);
    Debug("cdlist") << "save " << this << " at level "
                    << this->getContext()->getLevel() << " size at "
                    << this->d_size << " data:" << data << std::endl;
    return data;
  }

}; /* class CDList<> */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* CVC4__CONTEXT__CDLIST_H */
