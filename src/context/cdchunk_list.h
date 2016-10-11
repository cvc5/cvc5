/*********************                                                        */
/*! \file cdchunk_list.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Tim King, Clark Barrett
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Context-dependent list class designed for use with a
 ** context memory allocator.
 **
 ** Context-dependent list class designed for use with a context
 ** memory allocator.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CDCHUNK_LIST_H
#define __CVC4__CONTEXT__CDCHUNK_LIST_H

#include <iterator>
#include <memory>

#include "base/cvc4_assert.h"
#include "context/context.h"
#include "context/context_mm.h"


namespace CVC4 {
namespace context {

/**
 * Generic context-dependent dynamic array.  Like the usual CDList<>,
 * but allocates all memory from context memory.  Elements are kept in
 * cascading "list segments."  Access to elements by operator[] is not O(1) but
 * O(log n).  As with CDList<>, update is not permitted, only
 * appending to the end of the list.
 */
template <class T>
class CDChunkList : public ContextObj {
public:

  /** The value type with which this CDChunkList<> was instantiated. */
  typedef T value_type;
  /** The allocator type with which this CDChunkList<> was instantiated. */
  typedef ContextMemoryAllocator<T> Allocator;

protected:

  static const size_t INITIAL_SEGMENT_SIZE = 10;
  static const size_t INCREMENTAL_GROWTH_FACTOR = 2;

  /**
   * ListSegment is itself allocated in Context memory, but it is
   * never updated; it serves as information about the d_list segment
   * pointer it contains only.
   */
  class ListSegment {
    ListSegment* d_nextSegment;
    size_t d_segmentSize;
    T* d_list;
  public:
    ListSegment() :
      d_nextSegment(NULL),
      d_segmentSize(0),
      d_list(NULL) {
    }
    void initialize(T* list) {
      Assert( d_nextSegment == NULL &&
              d_segmentSize == 0 &&
              d_list == NULL,
              "Double-initialization of ListSegment not permitted" );
      d_list = list;
    }
    void linkTo(ListSegment* nextSegment) {
      Assert( d_nextSegment == NULL,
              "Double-linking of ListSegment not permitted" );
      d_nextSegment = nextSegment;
    }
    void cutLink() {
      d_nextSegment = NULL;
    }
    ListSegment* getNextSegment() const { return d_nextSegment; }
    size_t& size() { return d_segmentSize; }
    size_t size() const { return d_segmentSize; }
    const T* list() const { return d_list; }
    T& operator[](size_t i) { return d_list[i]; }
    const T& operator[](size_t i) const { return d_list[i]; }
  };/* struct CDChunkList<T>::ListSegment */

  /**
   * The first segment of list memory.
   */
  ListSegment d_headSegment;

  /**
   * A pointer to the final segment of list memory.
   */
  ListSegment* d_tailSegment;

  /**
   * Whether to call the destructor when items are popped from the
   * list.  True by default, but can be set to false by setting the
   * second argument in the constructor to false.
   */
  bool d_callDestructor;

  /**
   * Number of objects in list across all segments.
   */
  size_t d_size;

  /**
   * Total allocated size across all segments.
   */
  size_t d_totalSizeAlloc;

  /**
   * Our allocator.
   */
  Allocator d_allocator;

  /**
   * Lightweight save object for CDChunkList<T, ContextMemoryAllocator<T> >.
   */
  struct CDChunkListSave : public ContextObj {
    ListSegment* d_tail;
    size_t d_tailSize, d_size, d_sizeAlloc;
    CDChunkListSave(const CDChunkList<T>& list, ListSegment* tail,
               size_t size, size_t sizeAlloc) :
      ContextObj(list),
      d_tail(tail),
      d_tailSize(tail->size()),
      d_size(size),
      d_sizeAlloc(sizeAlloc) {
    }
    ~CDChunkListSave() {
      this->destroy();
    }
    ContextObj* save(ContextMemoryManager* pCMM) {
      // This type of object _is_ the save/restore object.  It isn't
      // itself saved or restored.
      Unreachable();
    }
    void restore(ContextObj* data) {
      // This type of object _is_ the save/restore object.  It isn't
      // itself saved or restored.
      Unreachable();
    }
  };/* struct CDChunkList<T>::CDChunkListSave */

  /**
   * Private copy constructor undefined (no copy permitted).
   */
  CDChunkList(const CDChunkList<T>& l) CVC4_UNDEFINED;

  /**
   * Allocate the first list segment.
   */
  void allocateHeadSegment() {
    Assert(d_headSegment.list() == NULL);
    Assert(d_totalSizeAlloc == 0 && d_size == 0);

    // Allocate an initial list if one does not yet exist
    size_t newSize = INITIAL_SEGMENT_SIZE;
    Debug("cdlist:cmm") << "initial grow of cdlist " << this
                        << " level " << getContext()->getLevel()
                        << " to " << newSize << std::endl;
    if(newSize > d_allocator.max_size()) {
      newSize = d_allocator.max_size();
    }
    T* newList = d_allocator.allocate(newSize);
    if(newList == NULL) {
      throw std::bad_alloc();
    }
    d_totalSizeAlloc = newSize;
    d_headSegment.initialize(newList);
  }

  /**
   * Allocate a new segment with more space.
   * Throws bad_alloc if memory allocation fails.
   */
  void grow() {
    Assert(d_totalSizeAlloc == d_size);

    // Allocate a new segment
    typedef typename Allocator::template rebind<ListSegment>::other
      SegmentAllocator;
    ContextMemoryManager* cmm = d_allocator.getCMM();
    SegmentAllocator segAllocator = SegmentAllocator(cmm);
    ListSegment* newSegment = segAllocator.allocate(1);
    if(newSegment == NULL) {
      throw std::bad_alloc();
    }
    segAllocator.construct(newSegment, ListSegment());
    size_t newSize = INCREMENTAL_GROWTH_FACTOR * d_totalSizeAlloc;
    if(newSize > d_allocator.max_size()) {
      newSize = d_allocator.max_size();
    }
    T* newList = d_allocator.allocate(newSize);
    Debug("cdlist:cmm") << "new segment of cdlistcontext " << this
                        << " level " << getContext()->getLevel()
                        << " to " << newSize
                        << " (from " << d_tailSegment->list()
                        << " to " << newList << ")" << std::endl;
    if(newList == NULL) {
      throw std::bad_alloc();
    }
    d_tailSegment->linkTo(newSegment);
    d_tailSegment = newSegment;
    d_tailSegment->initialize(newList);
    d_totalSizeAlloc += newSize;
  }

  /**
   * Implementation of mandatory ContextObj method save: simply copies the
   * current size to a copy using the copy constructor (the pointer and the
   * allocated size are *not* copied as they are not restored on a pop).
   * The saved information is allocated using the ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) {
    ContextObj* data = new(pCMM) CDChunkListSave(*this, d_tailSegment,
                                            d_size, d_totalSizeAlloc);
    Debug("cdlist:cmm") << "save " << this
                        << " at level " << this->getContext()->getLevel()
                        << " size at " << this->d_size
                        << " totalSizeAlloc at " << this->d_totalSizeAlloc
                        << " data:" << data << std::endl;
    return data;
  }

  /**
   * Implementation of mandatory ContextObj method restore: simply restores the
   * previous size.  Note that the list pointer and the allocated size are not
   * changed.
   */
  void restore(ContextObj* data) {
    CDChunkListSave* save = static_cast<CDChunkListSave*>(data);
    Debug("cdlist:cmm") << "restore " << this
                        << " level " << this->getContext()->getLevel()
                        << " data == " << data
                        << " call dtor == " << this->d_callDestructor
                        << " d_tail == " << this->d_tailSegment << std::endl;
    if(this->d_callDestructor) {
      ListSegment* seg = &d_headSegment;
      size_t i = save->d_size;
      while(i >= seg->size()) {
        i -= seg->size();
        seg = seg->getNextSegment();
      }
      do {
        while(i < seg->size()) {
          this->d_allocator.destroy(&(*seg)[i++]);
        }
        i = 0;
      } while((seg = seg->getNextSegment()) != NULL);
    }

    this->d_size = save->d_size;
    this->d_tailSegment = save->d_tail;
    this->d_tailSegment->size() = save->d_tailSize;
    this->d_tailSegment->cutLink();
    this->d_totalSizeAlloc = save->d_sizeAlloc;
    Debug("cdlist:cmm") << "restore " << this
                        << " level " << this->getContext()->getLevel()
                        << " size back to " << this->d_size
                        << " totalSizeAlloc at " << this->d_totalSizeAlloc
                        << std::endl;
  }

public:

  CDChunkList(Context* context, bool callDestructor, const Allocator& alloc) :
    ContextObj(context),
    d_headSegment(),
    d_tailSegment(&d_headSegment),
    d_callDestructor(callDestructor),
    d_size(0),
    d_totalSizeAlloc(0),
    d_allocator(alloc) {
    allocateHeadSegment();
  }

  CDChunkList(Context* context, bool callDestructor = true) :
    ContextObj(context),
    d_headSegment(),
    d_tailSegment(&d_headSegment),
    d_callDestructor(callDestructor),
    d_size(0),
    d_totalSizeAlloc(0),
    d_allocator(Allocator(context->getCMM())) {
    allocateHeadSegment();
  }

  CDChunkList(bool allocatedInCMM, Context* context, bool callDestructor,
         const Allocator& alloc) :
    ContextObj(allocatedInCMM, context),
    d_headSegment(),
    d_tailSegment(&d_headSegment),
    d_callDestructor(callDestructor),
    d_size(0),
    d_totalSizeAlloc(0),
    d_allocator(alloc) {
    allocateHeadSegment();
  }

  CDChunkList(bool allocatedInCMM, Context* context, bool callDestructor = true) :
    ContextObj(allocatedInCMM, context),
    d_headSegment(),
    d_tailSegment(&d_headSegment),
    d_callDestructor(callDestructor),
    d_size(0),
    d_totalSizeAlloc(0),
    d_allocator(Allocator(context->getCMM())) {
    allocateHeadSegment();
  }

  /**
   * Destructor: delete the list
   */
  ~CDChunkList() {
    this->destroy();

    if(this->d_callDestructor) {
      for(ListSegment* segment = &d_headSegment;
          segment != NULL;
          segment = segment->getNextSegment()) {
        for(size_t i = 0; i < segment->size(); ++i) {
          this->d_allocator.destroy(&(*segment)[i]);
        }
      }
    }
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
    Debug("cdlist:cmm") << "push_back " << this
                        << " level " << getContext()->getLevel()
                        << ": make-current, "
                        << "d_list == " << d_tailSegment->list() << std::endl;
    makeCurrent();

    Debug("cdlist:cmm") << "push_back " << this
                        << " level " << getContext()->getLevel()
                        << ": grow? " << d_size
                        << " size_alloc " << d_totalSizeAlloc
                        << std::endl;

    if(d_size == d_totalSizeAlloc) {
      Debug("cdlist:cmm") << "push_back " << this
                          << " " << getContext()->getLevel()
                          << ": grow!\n";
      grow();
    }
    Assert(d_size < d_totalSizeAlloc);

    Debug("cdlist:cmm") << "push_back " << this
                        << " " << getContext()->getLevel()
                        << ": construct! at [" << d_size << "] == "
                        << &(*d_tailSegment)[d_tailSegment->size()]
                        << std::endl;
    d_allocator.construct(&(*d_tailSegment)[d_tailSegment->size()], data);
    Debug("cdlist:cmm") << "push_back " << this
                        << " " << getContext()->getLevel()
                        << ": done..." << std::endl;
    ++d_tailSegment->size();
    ++d_size;
    Debug("cdlist:cmm") << "push_back " << this
                        << " " << getContext()->getLevel()
                        << ": size now " << d_size << std::endl;
  }

  /**
   * Access to the ith item in the list in O(log n).
   */
  const T& operator[](size_t i) const {
    Assert(i < d_size, "index out of bounds in CDChunkList::operator[]");
    const ListSegment* seg = &d_headSegment;
    while(i >= seg->size()) {
      i -= seg->size();
      seg = seg->getNextSegment();
    }
    return (*seg)[i];
  }

  /**
   * Returns the most recent item added to the list.
   */
  const T& back() const {
    Assert(d_size > 0, "CDChunkList::back() called on empty list");
    return (*d_tailSegment)[d_tailSegment->size() - 1];
  }

  /**
   * Iterator for CDChunkList class.  It has to be const because we don't
   * allow items in the list to be changed.  It's a straightforward
   * wrapper around a pointer.  Note that for efficiency, we implement
   * only prefix increment and decrement.  Also note that it's OK to
   * create an iterator from an empty, uninitialized list, as begin()
   * and end() will have the same value (NULL).
   */
  class const_iterator {
    const ListSegment* d_segment;
    size_t d_index;

    const_iterator(const ListSegment* segment, size_t i) :
      d_segment(segment),
      d_index(i) {
    }

    friend class CDChunkList<T>;

  public:

    typedef std::input_iterator_tag iterator_category;
    typedef T value_type;
    typedef std::ptrdiff_t difference_type;
    typedef const T* pointer;
    typedef const T& reference;

    const_iterator() : d_segment(NULL), d_index(0) {}

    inline bool operator==(const const_iterator& i) const {
      return d_segment == i.d_segment && d_index == i.d_index;
    }

    inline bool operator!=(const const_iterator& i) const {
      return !(*this == i);
    }

    inline const T& operator*() const {
      return (*d_segment)[d_index];
    }

    /** Prefix increment */
    const_iterator& operator++() {
      if(++d_index >= d_segment->size()) {
        d_segment = d_segment->getNextSegment();
        d_index = 0;
      }
      return *this;
    }

    /** Postfix increment: returns new iterator with the old value. */
    const_iterator operator++(int) {
      const_iterator i = *this;
      ++(*this);
      return i;
    }
  };/* class CDChunkList<>::const_iterator */

  /**
   * Returns an iterator pointing to the first item in the list.
   */
  const_iterator begin() const {
    // This looks curious, but we have to make sure that begin() == end()
    // for an empty list, and begin() == (head,0) for a nonempty one.
    // Since the segment spill-over is implemented in
    // iterator::operator++(), let's reuse it. */
    return ++const_iterator(&d_headSegment, -1);
  }

  /**
   * Returns an iterator pointing one past the last item in the list.
   */
  const_iterator end() const {
    return const_iterator(NULL, 0);
  }
};/* class CDChunkList<T, ContextMemoryAllocator<T> > */

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CDCHUNK_LIST_H */
