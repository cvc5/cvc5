/*********************                                                        */
/** context.h
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): taking, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Context class and context manager.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CONTEXT_H
#define __CVC4__CONTEXT__CONTEXT_H

#include "context/context_mm.h"
#include "util/Assert.h"
#include <cstdlib>
#include <cstring>
#include <new>

namespace CVC4 {
namespace context {

class Context;
class Scope;
class ContextObj;
class ContextNotifyObj;

  /**
   * A Context encapsulates all of the dynamic state of the system.  Its main
   * methods are push() and pop().  A call to push() saves the current state,
   * and a call to pop() restores the state saved by the most recent call to
   * push().
   *
   * Objects which want to participate in this global save and restore
   * mechanism must inherit from ContextObj (see below).
   *
   * For more flexible context-dependent behavior, objects may implement the
   * ContextNotifyObj interface and simply get a notification when a pop has
   * occurred.
   *
   * Context also uses a helper class called Scope which stores information
   * specific to the portion of the Context since the last call to push() (see
   * below).
   *
   * Memory allocation in Contexts is done with the help of the
   * ContextMemoryManager.  A copy is stored in each Scope object for quick
   * access.
   *
   */
class Context {

  /**
   * Pointer to the ContextMemoryManager for this Context.
   */
  ContextMemoryManager* d_pCMM;

  /**
   * List of all scopes for this context.
   */
  std::vector<Scope*> d_scopeList;

  /**
   * Doubly-linked list of objects to notify before every pop.  See
   * ContextNotifyObj for structure of linked list.
   */
  ContextNotifyObj* d_pCNOpre;

  /**
   * Doubly-linked list of objects to notify after every pop.  See
   * ContextNotifyObj for structure of linked list.
   */
  ContextNotifyObj* d_pCNOpost;

public:
  /**
   * Constructor: create ContextMemoryManager and initial Scope
   */
  Context();

  /**
   * Destructor: pop all scopes, delete ContextMemoryManager
   */
  ~Context();

  /**
   * Return the current (top) scope
   */
  Scope* getTopScope() const { return d_scopeList.back(); }

  /**
   * Return the initial (bottom) scope
   */
  Scope* getBottomScope() const { return d_scopeList[0]; }

  /**
   * Return the current Scope level.
   */
  int getLevel() const { return ((int)d_scopeList.size()) - 1; }

  /**
   * Return the ContextMemoryManager associated with the context.
   */
  ContextMemoryManager* getCMM(){ return d_pCMM; }

  /**
   * Save the current state, create a new Scope
   */
  void push();

  /**
   * Restore the previous state, delete the top Scope
   */
  void pop();

  /**
   * Pop all the way back to given level
   */
  void popto(int toLevel);

  /**
   * Add pCNO to the list of objects notified before every pop
   */
  void addNotifyObjPre(ContextNotifyObj* pCNO);

  /**
   * Add pCNO to the list of objects notified after every pop
   */
  void addNotifyObjPost(ContextNotifyObj* pCNO);

}; /* class Context */

  /**
   * Conceptually, a Scope encapsulates that portion of the context that
   * changes after a call to push() and must be undone on a subsequent call to
   * pop().  In particular, each call to push() creates a new Scope object .
   * This new Scope object becomes the top scope and it points (via the
   * d_pScopePrev member) to the previous top Scope.  Each call to pop()
   * deletes the current top scope and restores the previous one.  The main
   * purpose of a Scope is to maintain a linked list of ContexObj objects which
   * change while the Scope is the top scope and which must be restored when
   * the Scope is deleted.
   *
   * A Scope is also associated with a ContextMemoryManager.  All memory
   * allocated by the Scope is allocated in a single region using the
   * ContextMemoryManager and released all at once when the Scope is popped.
   */
class Scope {

  /**
   * Context that created this Scope
   */
  Context* d_pContext;

  /**
   * Memory manager for this Scope.  Same as in Context, but stored here too
   * for faster access by ContextObj objects.
   */
  ContextMemoryManager* d_pCMM;

  /**
   * Scope level (total number of outstanding push() calls when this Scope was
   * created).
   */
  int d_level;

  /**
   * Linked list of objects which changed in this scope,
   * and thus need to be restored when the scope is deleted.
   */
  ContextObj* d_pContextObjList;

public:

  /**
   * Constructor: Create a new Scope; set the level and the previous Scope
   * if any.
   */
  Scope(Context* pContext, ContextMemoryManager* pCMM, int level)
    : d_pContext(pContext), d_pCMM(pCMM), d_level(level),
      d_pContextObjList(NULL) { }

  /**
   * Destructor: Restore all of the objects in ContextObjList.  Defined inline
   * below.
   */
  ~Scope();

  /**
   * Get the Context for this Scope
   */
  Context* getContext() const { return d_pContext; }

  /**
   * Get the ContextMemoryManager for this Scope
   */
  ContextMemoryManager* getCMM() const { return d_pCMM; }

  /**
   * Get the level of the current Scope
   */
  int getLevel(void) const { return d_level; }

  /**
   * Return true iff this Scope is the current top Scope
   */
  bool isCurrent(void) const { return this == d_pContext->getTopScope(); }

  /**
   * When a ContextObj object is modified for the first time in this Scope, it
   * should call this method to add itself to the list of objects that will
   * need to be restored.  Defined inline below.
   */
  void addToChain(ContextObj* pContextObj);

  /**
   * Overload operator new for use with ContextMemoryManager to allow creation
   * of new Scope objects in the current memory region.
   */
  static void* operator new(size_t size, ContextMemoryManager* pCMM)
    { return pCMM->newData(size); }

  /**
   * Overload operator delete for Scope objects allocated using
   * ContextMemoryManager.  No need to do anything because memory is freed
   * automatically when the ContextMemoryManager pop() method is called.
   * Include both placement and standard delete for completeness.
   */
  static void operator delete(void* pMem, ContextMemoryManager* pCMM) { }
  static void operator delete(void* pMem) { }

  //FIXME:  //! Check for memory leaks
  //  void check(void);

}; /* class Scope */

  /**
   * This is an abstract base class from which all objects that are context-dependent
   * should inherit.  For any data structure that you want to have be
   * automatically backtracked, do the following:
   * 1. Create a class for the data structure that inherits from ContextObj
   * 2. Implement save()
   *    The role of save() is to create a new ContexObj object that contains
   *    enough information to restore the object to its current state, even if
   *    it gets changed later.  Note that save should call the (default)
   *    ContextObj Copy Constructor to copy the information in the base class.
   *    It is recommended that any memory allocated by save() should be done
   *    through the ContextMemoryManager.  This way, it does not need to be
   *    explicitly freed when restore is called.  However, it is only required
   *    that the ContextObj itself be allocated using the
   *    ContextMemoryManager.  If other memory is allocated not using the
   *    ContextMemoryManager, it should be freed when restore() is called.  In
   *    fact, any clean-up work on a saved object must be done by restore().
   *    This is because the destructor is never called explicitly on saved
   *    objects.
   * 3. Implement restore()
   *    The role of restore() is, given the ContextObj returned by a previous
   *    call to save(), to restore the current object to the state it was in
   *    when save() was called.  Note that the implementation of restore does
   *    *not* need to worry about restoring the base class data.  This is done
   *    automatically.  Ideally, restore() should not have to free any memory
   *    as any memory allocated by save() should have been done using the
   *    ContextMemoryManager (see item 2 above).
   * 4. In the subclass implementation, any time the state is about to be
   *    changed, first call makeCurrent().
   */
class ContextObj {
  /**
   * Pointer to Scope in which this object was last modified.
   */
  Scope* d_pScope; 

  /**
   * Pointer to most recent version of same ContextObj in a previous Scope
   */
  ContextObj* d_pContextObjRestore;

  /**
   * Next link in ContextObjList list maintained by Scope class.
   */
  ContextObj* d_pContextObjNext;

  /**
   * Previous link in ContextObjList list maintained by Scope class.  We use
   * double-indirection here to make element deletion easy.
   */
  ContextObj** d_ppContextObjPrev;

  /**
   * Helper method for makeCurrent (see below).  Separated out to allow common
   * case to be inlined without making a function call.  It calls save() and
   * does the necessary bookkeeping to ensure that object can be restored to
   * its current state when restore is called.
   */
  void update();

  // The rest of the private methods are for the benefit of the Scope.  We make
  // Scope our friend so it is the only one that can use them.

  friend class Scope;

  /**
   * Return reference to next link in ContextObjList.  Used by
   * Scope::addToChain method.
   */
  ContextObj*& next() { return d_pContextObjNext; }

  /**
   * Return reference to prev link in ContextObjList.  Used by
   * Scope::addToChain method.
   */
  ContextObj**& prev() { return d_ppContextObjPrev; }

  /**
   * This method is called by Scope during a pop: it does the necessary work to
   * restore the object from its saved copy and then returns the next object in
   * the list that needs to be restored.
   */
  ContextObj* restoreAndContinue();

protected:
  /**
   * This is a method that must be implemented by all classes inheriting from
   * ContextObj.  See the comment before the class declaration.
   */
  virtual ContextObj* save(ContextMemoryManager* pCMM) = 0;

  /**
   * This is a method that must be implemented by all classes inheriting from
   * ContextObj.  See the comment before the class declaration.
   */
  virtual void restore(ContextObj* pContextObjRestore) = 0;

  /**
   * This method checks if the object has been modified in this Scope yet.  If
   * not, it calls update().
   */
  void makeCurrent() { if (!(d_pScope->isCurrent())) update(); }

  /**
   * operator new using ContextMemoryManager (common case used by subclasses
   * during save() ).  No delete is required for memory allocated this way,
   * since it is automatically released when the context is popped.  Also note
   * that allocations using this operator never have their destructor called,
   * so any clean-up has to be done using the restore method.
   */
  static void* operator new(size_t size, ContextMemoryManager* pCMM) {
    return pCMM->newData(size);
  }

  /**
   * Corresponding placement delete.  Note that this is provided just to
   * satisfy the requirement that a placement delete should be provided for
   * every placement new.  It would only be called if a ContextObj Constructor
   * throws an exception after a successful call to the above new operator.
   */
  static void operator delete(void* pMem, ContextMemoryManager* pCMM) { }

public:
  /**
   * Create a new ContextObj.  The initial scope is set to the bottom
   * scope of the Context.  Note that in the common case, the copy constructor
   * is called to create new ContextObj objects.  The default copy constructor
   * does the right thing, so we do not explicitly define it.
   */
  ContextObj(Context* context);

  /**
   * Destructor: Calls restore until restored to initial version.  Also removes
   * object from all Scope lists.  Note that this doesn't actually free the
   * memory allocated by the ContextMemoryManager for this object.  This isn't
   * done until the corresponding Scope is popped.
   */
  virtual ~ContextObj();

  /**
   * If you want to allocate a ContextObj object on the heap, use this special
   * new operator.  To free this memory, instead of "delete p", use
   * "p->deleteSelf()".
   */
  static void* operator new(size_t size, bool) { return ::operator new(size); }

  /**
   * Corresponding placement delete.  Note that this is provided for the
   * compiler in case the ContextObj constructor throws an exception.  The
   * client can't call it.
   */
  static void operator delete(void* pMem, bool) { ::operator delete(pMem); }

  /**
   * Use this instead of delete to delete memory allocated using the special
   * new function provided above that takes a bool argument.  Do not call this
   * function on memory allocated using the new that takes a
   * ContextMemoryManager as an argument.
   */
  void deleteSelf() { ::operator delete(this); }

  /**
   * Disable delete: objects allocated with new(ContextMemorymanager) should
   * never be deleted.  Objects allocated with new(bool) should be deleted by
   * calling deleteSelf().
   */
  static void operator delete(void* pMem) {
    AlwaysAssert(false, "Not Allowed!");
  }

}; /* class ContextObj */

  /**
   * For more flexible context-dependent behavior than that provided by
   * ContextObj, objects may implement the ContextNotifyObj interface and
   * simply get a notification when a pop has occurred.  See Context class for
   * how to register a ContextNotifyObj with the Context (you can choose to
   * have notification come before or after the ContextObj objects have been
   * restored).
   */
class ContextNotifyObj {
  /**
   * Context is our friend so that when the Context is deleted, any remaining
   * ContextNotifyObj can be removed from the Context list.
   */
  friend class Context;

  /**
   * Pointer to next ContextNotifyObject in this List
   */
  ContextNotifyObj* d_pCNOnext;

  /**
   * Pointer to previous ContextNotifyObject in this list
   */
  ContextNotifyObj** d_ppCNOprev;

  /**
   * Return reference to next link in ContextNotifyObj list.  Used by
   * Context::addNotifyObj methods.
   */
  ContextNotifyObj*& next() { return d_pCNOnext; }

  /**
   * Return reference to prev link in ContextNotifyObj list.  Used by
   * Context::addNotifyObj methods.
   */
  ContextNotifyObj**& prev() { return d_ppCNOprev; }

public:
  /**
   * Constructor for ContextNotifyObj.  Parameters are the context to which
   * this notify object will be added, and a flag which, if true, tells the
   * context to notify this object *before* the ContextObj objects are
   * restored.  Otherwise, the context notifies the object after the ContextObj
   * objects are restored.  The default is for notification after.
   */
  ContextNotifyObj(Context* pContext, bool preNotify = false);

  /**
   * Destructor: removes object from list
   */
  virtual ~ContextNotifyObj();

  /**
   * This is the method called to notify the object of a pop.  It must be
   * implemented by the subclass.
   */
  virtual void notify() = 0;
}; /* class ContextNotifyObj */

// Inline functions whose definitions had to be delayed:

inline Scope::~Scope() {
  // Call restore() method on each ContextObj object in the list.
  // Note that it is the responsibility of restore() to return the next item in
  // the list.
  while (d_pContextObjList != NULL) {
    d_pContextObjList = d_pContextObjList->restoreAndContinue();
  }
}

inline void Scope::addToChain(ContextObj* pContextObj) {
  if(d_pContextObjList != NULL)
    d_pContextObjList->prev() = &(pContextObj->next());
  pContextObj->next() = d_pContextObjList;
  pContextObj->prev() = &d_pContextObjList;
  d_pContextObjList = pContextObj;
}

  /**
   * Most basic template for context-dependent objects.  Simply makes a copy
   * (using the copy constructor) of class T when saving, and copies it back
   * (using operator=) during restore.
   */
template <class T>
class CDO :public ContextObj {

  /**
   * The data of type T being stored in this context-dependent object.
   */
  T d_data;

  /**
   * Implementation of mandatory ContextObj method save: simply copies the
   * current data to a copy using the copy constructor.  Memory is allocated
   * using the ContextMemoryManager.
   */
  virtual ContextObj* save(ContextMemoryManager* pCMM) {
    return new(pCMM) CDO<T>(*this);
  }

  /**
   * Implementation of mandatory ContextObj method restore: simply copies the
   * saved data back from the saved copy using operator= for T.
   */
  virtual void restore(ContextObj* pContextObj) {
    d_data = ((CDO<T>*)pContextObj)->d_data;
  }

  /**
   * Copy constructor - it's private to ensure it is only used by save().
   * Basic CDO objects, cannot be copied-they have to be unique.
   */
  CDO(const CDO<T>& cdo): ContextObj(cdo), d_data(cdo.d_data) { }

  /**
   * operator= for CDO is private to ensure CDO object is not copied.
   */
  CDO<T>& operator=(const CDO<T>& cdo) {}

public:
  /**
   * Main constructor - uses default constructor for T to create the initial
   * value of d_data.
   */
  CDO(Context* context) : ContextObj(context) {}

  /**
   * Constructor from object of type T.  Creates a ContextObj and sets the data
   * to the given data value.  Note that this value is only valid in the
   * current Scope.  If the Scope is popped, the value will revert to whatever
   * is assigned by the default constructor for T
   */
  CDO(Context* context, const T& data) : ContextObj(context) {
    makeCurrent(); d_data = data;
  }

  /**
   * Destructor - no need to do anything.
   */
  ~CDO() {}

  /**
   * Set the data in the CDO.  First call makeCurrent.
   */
  void set(const T& data) { makeCurrent(); d_data = data; }

  /**
   * Get the current data from the CDO.  Read-only.
   */
  const T& get() const { return d_data; }

  /**
   * For convenience, define operator T to be the same as get().
   */
  operator T() { return get(); }

  /**
   * For convenience, define operator= that takes an object of type T.
   */
  CDO<T>& operator=(const T& data) { set(data); return *this; }

}; /* class CDO */

  /**
   * Generic context-dependent dynamic array.  Note that for efficiency, this
   * implementation makes the following assumptions:
   * 1. Over time, objects are only added to the list.  Objects are only
   *    removed when a pop restores the list to a previous state.
   * 2. T objects can safely be copied using their copy constructor,
   *    operator=, and memcpy.
   */
template <class T>
class CDList :public ContextObj {
  /**
   * d_list is a dynamic array of objects of type T.
   */
  T* d_list;

  /**
   * Whether to call the destructor when items are popped from the
   * list.  True by default, but can be set to false by setting the
   * second argument in the constructor to false.
   */
  bool d_callDestructor;

  /**
   * Number of objects in d_list
   */
  unsigned d_size;

  /**
   * Allocated size of d_list.
   */
  unsigned d_sizeAlloc;

  /**
   * Implementation of mandatory ContextObj method save: simply copies the
   * current size to a copy using the copy constructor (the pointer and the
   * allocated size are *not* copied as they are not restored on a pop).
   * The saved information is allocated using the ContextMemoryManager.
   */
  ContextObj* save(ContextMemoryManager* pCMM) {
    return new(pCMM) CDList<T>(*this);
  }

  /**
   * Implementation of mandatory ContextObj method restore: simply restores the
   * previous size.  Note that the list pointer and the allocated size are not
   * changed.
   */
  void restore(ContextObj* data) {
    if (d_callDestructor) {
      unsigned size = ((CDList<T>*)data)->d_size;
      while (d_size != size) {
        --d_size;
        d_list[d_size].~T();
      }
    }
    else {
      d_size = ((CDList<T>*)data)->d_size;
    }
  }

  /**
   * Privae copy constructor used only by save above.  d_list and d_sizeAlloc
   * are not copied: only the base class information and d_size are needed in
   * restore.
   */
  CDList(const CDList<T>& l): ContextObj(l), d_list(NULL),
                              d_size(l.d_size), d_sizeAlloc(0) { }

  /**
   * Reallocate the array with more space.
   * Throws bad_alloc if memory allocation fails.
   */
  void grow() {
    if (d_list == NULL) {
      // Allocate an initial list if one does not yet exist
      d_sizeAlloc = 10;
      d_list = (T*)malloc(sizeof(T)*d_sizeAlloc);
      if(d_list == NULL){
        throw std::bad_alloc();
      }
    }
    else {
      // Allocate a new array with double the size
      d_sizeAlloc *= 2;
      T* tmpList = (T*)realloc(d_list, sizeof(T)*d_sizeAlloc);
      if(tmpList == NULL){
        throw std::bad_alloc();
      }
      d_list = tmpList;
    }
  }

public:
  /**
   * Main constructor: d_list starts as NULL, size is 0
   */
 CDList(Context* context, bool callDestructor = true)
   : ContextObj(context), d_list(NULL), d_callDestructor(callDestructor),
    d_size(0), d_sizeAlloc(0) { }

  /**
   * Destructor: delete the list
   */
  ~CDList() {
    if(d_list != NULL) {
      if (d_callDestructor) {
        while (d_size != 0) {
          --d_size;
          d_list[d_size].~T();
        }
      }
      delete d_list;
    }
  }

  /**
   * Return the current size of (i.e. valid number of objects in) the list
   */
  unsigned size() const { return d_size; }


  /**
   * Return true iff there are no valid objects in the list.
   */
  bool empty() const { return d_size == 0; }

  /**
   * Add an item to the end of the list.
   */
  void push_back(const T& data) {
    makeCurrent();
    if (d_size == d_sizeAlloc) grow();
    ::new((void*)(d_list + d_size)) T(data);
    ++ d_size;
  }

  /**
   * operator[]: return the ith item in the list
   */
  const T& operator[](unsigned i) const {
    Assert(i < d_size, "index out of bounds in CDList::operator[]");
    return d_list[i];
  }

  /**
   * return the most recent item added to the list
   */
  const T& back() const {
    Assert(d_size > 0, "CDList::back() called on empty list");
    return d_list[d_size-1];
  }

  /**
   * Iterator for CDList class.  It has to be const because we don't allow
   * items in the list to be changed.  It's a straightforward wrapper around a
   * pointer.  Note that for efficiency, we implement only prefix increment and
   * decrement.  Also note that it's OK to create an iterator from an empty,
   * uninitialized list, as begin() and end() will have the same value (NULL).
   */
  class const_iterator {
    friend class CDList<T>;
    T* d_it;
    const_iterator(T* it) : d_it(it) {};
  public:
    const_iterator() : d_it(NULL) {}
    bool operator==(const const_iterator& i) const { return d_it == i.d_it; }
    bool operator!=(const const_iterator& i) const { return d_it != i.d_it; }
    const T& operator*() const { return *d_it; }
    /** Prefix increment */
    const_iterator& operator++() { ++d_it; return *this; }
    /** Prefix decrement */
    const_iterator& operator--() { --d_it; return *this; }
  }; /* class const_iterator */

  /**
   * Returns an iterator pointing to the first item in the list.
   */
  const_iterator begin() const {
    return const_iterator(d_list);
  }

  /**
   * Returns an iterator pointing one past the last item in the list.
   */
  const_iterator end() const {
    return const_iterator(d_list + d_size);
  }

}; /* class CDList */

template <class T>
class CDMap;

template <class T>
class CDSet;

} /* CVC4::context namespace */

} /* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CONTEXT_H */

