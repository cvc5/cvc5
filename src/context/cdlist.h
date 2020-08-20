/*********************                                                        */
/*! \file cdlist.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
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
#include <string>
#include <sstream>

#include "base/check.h"
#include "context/cdlist_forward.h"
#include "context/context.h"
#include "context/context_mm.h"

namespace CVC4 {
namespace context {

/**
 * Generic context-dependent dynamic array.  Note that for efficiency,
 * this implementation makes the following assumptions:
 *
 * 1. Over time, objects are only added to the list.  Objects are only
 *    removed when a pop restores the list to a previous state.
 *
 * 2. T objects can safely be copied using their copy constructor,
 *    operator=, and memcpy.
 */
template <class T, class CleanUpT, class AllocatorT>
class CDList : public ContextObj {
public:

  /** The value type with which this CDList<> was instantiated. */
  typedef T value_type;

  /** The cleanup type with which this CDList<> was instantiated. */
  typedef CleanUpT CleanUp;

  /** The allocator type with which this CDList<> was instantiated. */
  typedef AllocatorT Allocator;

protected:

  /**
   * d_list is a dynamic array of objects of type T.
   */
  T* d_list;

  /**
   * Number of objects in d_list
   */
  size_t d_size;

private:

  static const size_t INITIAL_SIZE = 10;
  static const size_t GROWTH_FACTOR = 2;

  /**
   * Whether to call the destructor when items are popped from the
   * list.  True by default, but can be set to false by setting the
   * second argument in the constructor to false.
   */
  bool d_callDestructor;

  /**
   * Allocated size of d_list.
   */
  size_t d_sizeAlloc;

  /**
   * The CleanUp functor.
   */
  CleanUp d_cleanUp;

  /**
   * Our allocator.
   */
  Allocator d_allocator;

protected:
  /**
   * Private copy constructor used only by save().  d_list and
   * d_sizeAlloc are not copied: only the base class information and
   * d_size are needed in restore.
   */
  CDList(const CDList& l) :
    ContextObj(l),
    d_list(NULL),
    d_size(l.d_size),
    d_callDestructor(false),
    d_sizeAlloc(0),
    d_cleanUp(l.d_cleanUp),
    d_allocator(l.d_allocator) {
    Debug("cdlist") << "copy ctor: " << this
                    << " from " << &l
                    << " size " << d_size << std::endl;
  }
  CDList& operator=(const CDList& l) = delete;

private:
  /**
   * Reallocate the array with more space.
   * Throws bad_alloc if memory allocation fails.
   */
  void grow() {
    if(d_list == NULL) {
      // Allocate an initial list if one does not yet exist
      d_sizeAlloc = INITIAL_SIZE;
      Debug("cdlist") << "initial grow of cdlist " << this
                      << " level " << getContext()->getLevel()
                      << " to " << d_sizeAlloc << std::endl;
      if(d_sizeAlloc > d_allocator.max_size()) {
        d_sizeAlloc = d_allocator.max_size();
      }
      d_list = d_allocator.allocate(d_sizeAlloc);
      if(d_list == NULL) {
        throw std::bad_alloc();
      }
    } else {
      // Allocate a new array with double the size
      size_t newSize = GROWTH_FACTOR * d_sizeAlloc;
      if(newSize > d_allocator.max_size()) {
        newSize = d_allocator.max_size();
        Assert(newSize > d_sizeAlloc)
            << "cannot request larger list due to allocator limits";
      }
      T* newList = d_allocator.allocate(newSize);
      Debug("cdlist") << "2x grow of cdlist " << this
                      << " level " << getContext()->getLevel()
                      << " to " << newSize
                      << " (from " << d_list
                      << " to " << newList << ")" << std::endl;
      if(newList == NULL) {
        throw std::bad_alloc();
      }
      std::memcpy(newList, d_list, sizeof(T) * d_sizeAlloc);
      d_allocator.deallocate(d_list, d_sizeAlloc);
      d_list = newList;
      d_sizeAlloc = newSize;
    }
  }

  /**
   * Implementation of mandatory ContextObj method save: simply copies
   * the current size to a copy using the copy constructor (the
   * pointer and the allocated size are *not* copied as they are not
   * restored on a pop).  The saved information is allocated using the
   * ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) override
  {
    ContextObj* data = new(pCMM) CDList<T, CleanUp, Allocator>(*this);
    Debug("cdlist") << "save " << this
                    << " at level " << this->getContext()->getLevel()
                    << " size at " << this->d_size
                    << " sizeAlloc at " << this->d_sizeAlloc
                    << " d_list is " << this->d_list
                    << " data:" << data << std::endl;
    return data;
  }

protected:
  /**
   * Implementation of mandatory ContextObj method restore: simply
   * restores the previous size.  Note that the list pointer and the
   * allocated size are not changed.
   */
 void restore(ContextObj* data) override
 {
   Debug("cdlist") << "restore " << this << " level "
                   << this->getContext()->getLevel() << " data == " << data
                   << " call dtor == " << this->d_callDestructor
                   << " d_list == " << this->d_list << std::endl;
   truncateList(((CDList<T, CleanUp, Allocator>*)data)->d_size);
   Debug("cdlist") << "restore " << this << " level "
                   << this->getContext()->getLevel() << " size back to "
                   << this->d_size << " sizeAlloc at " << this->d_sizeAlloc
                   << std::endl;
  }

  /**
   * Given a size parameter smaller than d_size, truncateList()
   * removes the elements from the end of the list until d_size equals size.
   *
   * WARNING! You should only use this function when you know what you are doing.
   * This is a primitive operation with strange context dependent behavior!
   * It is up to the user of the function to ensure that the saved d_size values
   * at lower context levels are less than or equal to size.
   */
  void truncateList(const size_t size){
    Assert(size <= d_size);
    if(d_callDestructor) {
      while(d_size != size) {
        --d_size;
        d_cleanUp(&d_list[d_size]);
        d_allocator.destroy(&d_list[d_size]);
      }
    } else {
      d_size = size;
    }
  }


public:

  /**
   * Main constructor: d_list starts as NULL, size is 0
   */
  CDList(Context* context,
         bool callDestructor = true,
         const CleanUp& cleanup = CleanUp(),
         const Allocator& alloc = Allocator()) :
    ContextObj(context),
    d_list(NULL),
    d_size(0),
    d_callDestructor(callDestructor),
    d_sizeAlloc(0),
    d_cleanUp(cleanup),
    d_allocator(alloc) {
  }

  /**
   * Destructor: delete the list
   */
  ~CDList() {
    this->destroy();

    if(this->d_callDestructor) {
      truncateList(0);
    }

    this->d_allocator.deallocate(this->d_list, this->d_sizeAlloc);
  }

  /**
   * Return the current size of (i.e. valid number of objects in) the
   * list.
   */
  size_t size() const {
    return d_size;
  }

  /**
   * Return true iff there are no valid objects in the list.
   */
  bool empty() const {
    return d_size == 0;
  }

  /**
   * Add an item to the end of the list.
   */
  void push_back(const T& data) {
    Debug("cdlist") << "push_back " << this
                    << " " << getContext()->getLevel()
                    << ": make-current, "
                    << "d_list == " << d_list << std::endl;
    makeCurrent();

    Debug("cdlist") << "push_back " << this
                    << " " << getContext()->getLevel()
                    << ": grow? " << d_size
                    << " " << d_sizeAlloc << std::endl;
    if(d_size == d_sizeAlloc) {
      Debug("cdlist") << "push_back " << this
                      << " " << getContext()->getLevel()
                      << ": grow!" << std::endl;
      grow();
    }
    Assert(d_size < d_sizeAlloc);

    Debug("cdlist") << "push_back " << this
                    << " " << getContext()->getLevel()
                    << ": construct! at " << d_list
                    << "[" << d_size << "] == " << &d_list[d_size]
                    << std::endl;
    d_allocator.construct(&d_list[d_size], data);
    Debug("cdlist") << "push_back " << this
                    << " " << getContext()->getLevel()
                    << ": done..." << std::endl;
    ++d_size;
    Debug("cdlist") << "push_back " << this
                    << " " << getContext()->getLevel()
                    << ": size now " << d_size << std::endl;
  }

  /**
   * Access to the ith item in the list.
   */
  const T& operator[](size_t i) const {
    Assert(i < d_size) << "index out of bounds in CDList::operator[]";
    return d_list[i];
  }

  /**
   * Returns the most recent item added to the list.
   */
  const T& back() const {
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
    T const* d_it;

    const_iterator(T const* it) : d_it(it) {}

    friend class CDList<T, CleanUp, Allocator>;

  public:

    // FIXME we support operator--, but do we satisfy all the
    // requirements of a bidirectional iterator ?
    typedef std::input_iterator_tag iterator_category;
    typedef T value_type;
    typedef std::ptrdiff_t difference_type;
    typedef const T* pointer;
    typedef const T& reference;

    const_iterator() : d_it(NULL) {}

    inline bool operator==(const const_iterator& i) const {
      return d_it == i.d_it;
    }

    inline bool operator!=(const const_iterator& i) const {
      return d_it != i.d_it;
    }

    inline const T& operator*() const {
      return *d_it;
    }

    /** Prefix increment */
    const_iterator& operator++() {
      ++d_it;
      return *this;
    }

    /** Prefix decrement */
    const_iterator& operator--() { --d_it; return *this; }

    /** operator+ */
    const_iterator operator+(long signed int off) const {
      return const_iterator(d_it + off);
    }

    // Postfix operations on iterators: requires a Proxy object to
    // hold the intermediate value for dereferencing
    class Proxy {
      const T* d_t;

    public:

      Proxy(const T& p): d_t(&p) {}

      T& operator*() {
        return *d_t;
      }
    };/* class CDList<>::const_iterator::Proxy */

    /** Postfix increment: returns Proxy with the old value. */
    Proxy operator++(int) {
      Proxy e(*(*this));
      ++(*this);
      return e;
    }

    /** Postfix decrement: returns Proxy with the old value. */
    Proxy operator--(int) {
      Proxy e(*(*this));
      --(*this);
      return e;
    }

  };/* class CDList<>::const_iterator */
  typedef const_iterator iterator;

  /**
   * Returns an iterator pointing to the first item in the list.
   */
  const_iterator begin() const {
    return const_iterator(static_cast<T const*>(d_list));
  }

  /**
   * Returns an iterator pointing one past the last item in the list.
   */
  const_iterator end() const {
    return const_iterator(static_cast<T const*>(d_list) + d_size);
  }
};/* class CDList<> */

template <class T, class CleanUp>
class CDList<T, CleanUp, ContextMemoryAllocator<T> > : public ContextObj {
  /* CDList is incompatible for use with a ContextMemoryAllocator.
   *
   * Explanation:
   * If ContextMemoryAllocator is used and d_list grows at a deeper context
   * level the reallocated will be reallocated in a context memory region that
   * can be destroyed on pop. To support this, a full copy of d_list would have
   * to be made. As this is unacceptable for performance in other situations, we
   * do not do this.
   */

  static_assert(sizeof(T) == 0,
                "Cannot create a CDList with a ContextMemoryAllocator.");
};

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* CVC4__CONTEXT__CDLIST_H */
