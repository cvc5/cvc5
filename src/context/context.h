/*********************                                                        */
/*! \file context.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): taking, dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Context class and context manager.
 **
 ** Context class and context manager.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__CONTEXT__CONTEXT_H
#define __CVC4__CONTEXT__CONTEXT_H

#include <iostream>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <new>

#include "context/context_mm.h"
#include "util/Assert.h"

namespace CVC4 {
namespace context {

class Context;
class Scope;
class ContextObj;
class ContextNotifyObj;

/** Pretty-printing of Contexts (for debugging) */
std::ostream&
operator<<(std::ostream&, const Context&) throw(AssertionException);

/** Pretty-printing of Scopes (for debugging) */
std::ostream&
operator<<(std::ostream&, const Scope&) throw(AssertionException);

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

  friend std::ostream&
  operator<<(std::ostream&, const Context&) throw(AssertionException);

public:
  /**
   * Constructor: create ContextMemoryManager and initial Scope
   */
  Context();

  /**
   * Destructor: pop all scopes, delete ContextMemoryManager
   */
  ~Context() throw(AssertionException);

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
  int getLevel() const { return d_scopeList.size() - 1; }

  /**
   * Return the ContextMemoryManager associated with the context.
   */
  ContextMemoryManager* getCMM() { return d_pCMM; }

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

};/* class Context */

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

  friend std::ostream&
  operator<<(std::ostream&, const Scope&) throw(AssertionException);

public:

  /**
   * Constructor: Create a new Scope; set the level and the previous Scope
   * if any.
   */
  Scope(Context* pContext, ContextMemoryManager* pCMM, int level) throw() :
    d_pContext(pContext),
    d_pCMM(pCMM),
    d_level(level),
    d_pContextObjList(NULL) {
  }

  /**
   * Destructor: Restore all of the objects in ContextObjList.  Defined inline
   * below.
   */
  ~Scope() throw(AssertionException);

  /**
   * Get the Context for this Scope
   */
  Context* getContext() const throw() { return d_pContext; }

  /**
   * Get the ContextMemoryManager for this Scope
   */
  ContextMemoryManager* getCMM() const throw() { return d_pCMM; }

  /**
   * Get the level of the current Scope
   */
  int getLevel() const throw() { return d_level; }

  /**
   * Return true iff this Scope is the current top Scope
   */
  bool isCurrent() const throw() { return this == d_pContext->getTopScope(); }

  /**
   * When a ContextObj object is modified for the first time in this
   * Scope, it should call this method to add itself to the list of
   * objects that will need to be restored.  Defined inline below.
   */
  void addToChain(ContextObj* pContextObj) throw(AssertionException);

  /**
   * Overload operator new for use with ContextMemoryManager to allow
   * creation of new Scope objects in the current memory region.
   */
  static void* operator new(size_t size, ContextMemoryManager* pCMM) {
    return pCMM->newData(size);
  }

  /**
   * Overload operator delete for Scope objects allocated using
   * ContextMemoryManager.  No need to do anything because memory is
   * freed automatically when the ContextMemoryManager pop() method is
   * called.  Include both placement and standard delete for
   * completeness.
   */
  static void operator delete(void* pMem, ContextMemoryManager* pCMM) {}
  static void operator delete(void* pMem) {}

  //FIXME:  //! Check for memory leaks
  //  void check();

};/* class Scope */

/**
 * This is an abstract base class from which all objects that are
 * context-dependent should inherit.  For any data structure that you
 * want to have be automatically backtracked, do the following:
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
 * 5. In the subclass implementation, the destructor should call destroy(),
 *    which repeatedly calls restore() until the object is restored to context
 *    level 0.  Note, however, that if there is additional cleanup required at
 *    level 0, destroy() does not do this.  It has to be implemented in the
 *    destructor of the subclass.  The reason the destroy() functionality
 *    cannot be in the ContextObj destructor is that it needs to call the
 *    subclass-specific restore() method in order to properly clean up saved
 *    copies.
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
  void update() throw(AssertionException);

  // The rest of the private methods are for the benefit of the Scope.  We make
  // Scope our friend so it is the only one that can use them.

  friend class Scope;

  friend std::ostream&
  operator<<(std::ostream&, const Scope&) throw(AssertionException);

  /**
   * Return reference to next link in ContextObjList.  Used by
   * Scope::addToChain method.
   */
  ContextObj*& next() throw() { return d_pContextObjNext; }

  /**
   * Return reference to prev link in ContextObjList.  Used by
   * Scope::addToChain method.
   */
  ContextObj**& prev() throw() { return d_ppContextObjPrev; }

  /**
   * This method is called by Scope during a pop: it does the necessary work to
   * restore the object from its saved copy and then returns the next object in
   * the list that needs to be restored.
   */
  ContextObj* restoreAndContinue() throw(AssertionException);

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
   * This method checks if the object has been modified in this Scope
   * yet.  If not, it calls update().
   */
  inline void makeCurrent() throw(AssertionException);

  /**
   * Should be called from sub-class destructor: calls restore until restored
   * to initial version (version at context level 0).  Also removes object from
   * all Scope lists.  Note that this doesn't actually free the memory
   * allocated by the ContextMemoryManager for this object.  This isn't done
   * until the corresponding Scope is popped.
   */
  void destroy() throw(AssertionException);

  /////
  //
  //  These next four accessors return properties of the Scope to
  //  derived classes without giving them the Scope object directly.
  //
  /////

  /**
   * Get the Context with which this ContextObj was created.  This is
   * part of the protected interface, intended for derived classes to
   * use if necessary.
   */
  Context* getContext() const throw() {
    return d_pScope->getContext();
  }

  /**
   * Get the ContextMemoryManager with which this ContextObj was
   * created.  This is part of the protected interface, intended for
   * derived classes to use if necessary.  If a ContextObj-derived
   * class needs to allocate memory somewhere other than the save()
   * member function (where it is explicitly given a
   * ContextMemoryManager), it can use this accessor to get the memory
   * manager.
   */
  ContextMemoryManager* getCMM() const throw() {
    return d_pScope->getCMM();
  }

  /**
   * Get the level associated to this ContextObj.  Useful if a
   * ContextObj-derived class needs to compare the level of its last
   * update with another ContextObj.
   */
  int getLevel() const throw() {
    return d_pScope->getLevel();
  }

  /**
   * Returns true if the object is "current"-- that is, updated in the
   * topmost contextual scope.  Useful if a ContextObj-derived class
   * needs to determine if it has been modified in the current scope.
   * Note that it is always safe to call makeCurrent() without first
   * checking if the object is current, so this function need not be
   * used under normal circumstances.
   */
  bool isCurrent() const throw() {
    return d_pScope->isCurrent();
  }

  /**
   * operator new using ContextMemoryManager (common case used by
   * subclasses during save()).  No delete is required for memory
   * allocated this way, since it is automatically released when the
   * context is popped.  Also note that allocations using this
   * operator never have their destructor called, so any clean-up has
   * to be done using the restore method.
   */
  static void* operator new(size_t size, ContextMemoryManager* pCMM) {
    return pCMM->newData(size);
  }

  /**
   * Corresponding placement delete.  Note that this is provided just
   * to satisfy the requirement that a placement delete should be
   * provided for every placement new.  It would only be called if a
   * ContextObj constructor throws an exception after a successful
   * call to the above new operator.
   */
  static void operator delete(void* pMem, ContextMemoryManager* pCMM) {}

public:

  /**
   * Create a new ContextObj.  The initial scope is set to the bottom
   * scope of the Context.  Note that in the common case, the copy
   * constructor is called to create new ContextObj objects.  The
   * default copy constructor does the right thing, so we do not
   * explicitly define it.
   */
  ContextObj(Context* context);

  /**
   * Create a new ContextObj.  This constructor takes an argument that
   * specifies whether this ContextObj is itself allocated in context
   * memory.  If it is, it's invalid below the current scope level, so
   * we don't put it in scope 0.
   */
  ContextObj(bool allocatedInCMM, Context* context);

  /**
   * Destructor does nothing: subclass must explicitly call destroy() instead.
   */
  virtual ~ContextObj() {}

  /**
   * If you want to allocate a ContextObj object on the heap, use this
   * special new operator.  To free this memory, instead of
   * "delete p", use "p->deleteSelf()".
   */
  static void* operator new(size_t size, bool) {
    return ::operator new(size);
  }

  /**
   * Corresponding placement delete.  Note that this is provided for
   * the compiler in case the ContextObj constructor throws an
   * exception.  The client can't call it.
   */
  static void operator delete(void* pMem, bool) {
    ::operator delete(pMem);
  }

  /**
   * Use this instead of delete to delete memory allocated using the special
   * new function provided above that takes a bool argument.  Do not call this
   * function on memory allocated using the new that takes a
   * ContextMemoryManager as an argument.
   */
  void deleteSelf() {
    Debug("context") << "deleteSelf(" << this << ")" << std::endl;
    this->~ContextObj();
    ::operator delete(this);
  }

  /**
   * Disable delete: objects allocated with new(ContextMemorymanager) should
   * never be deleted.  Objects allocated with new(bool) should be deleted by
   * calling deleteSelf().
   */
  static void operator delete(void* pMem) {
    AlwaysAssert(false, "It is not allowed to delete a ContextObj this way!");
  }

};/* class ContextObj */

/**
 * For more flexible context-dependent behavior than that provided by
 * ContextObj, objects may implement the ContextNotifyObj interface
 * and simply get a notification when a pop has occurred.  See
 * Context class for how to register a ContextNotifyObj with the
 * Context (you can choose to have notification come before or after
 * the ContextObj objects have been restored).
 */
class ContextNotifyObj {
  /**
   * Context is our friend so that when the Context is deleted, any
   * remaining ContextNotifyObj can be removed from the Context list.
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
  ContextNotifyObj*& next() throw() { return d_pCNOnext; }

  /**
   * Return reference to prev link in ContextNotifyObj list.  Used by
   * Context::addNotifyObj methods.
   */
  ContextNotifyObj**& prev() throw() { return d_ppCNOprev; }

public:

  /**
   * Constructor for ContextNotifyObj.  Parameters are the context to
   * which this notify object will be added, and a flag which, if
   * true, tells the context to notify this object *before* the
   * ContextObj objects are restored.  Otherwise, the context notifies
   * the object after the ContextObj objects are restored.  The
   * default is for notification after.
   */
  ContextNotifyObj(Context* pContext, bool preNotify = false);

  /**
   * Destructor: removes object from list
   */
  virtual ~ContextNotifyObj() throw(AssertionException);

  /**
   * This is the method called to notify the object of a pop.  It must be
   * implemented by the subclass.
   */
  virtual void notify() = 0;

};/* class ContextNotifyObj */

inline void ContextObj::makeCurrent() throw(AssertionException) {
  if(!(d_pScope->isCurrent())) {
    update();
  }
}

inline Scope::~Scope() throw(AssertionException) {
  // Call restore() method on each ContextObj object in the list.
  // Note that it is the responsibility of restore() to return the
  // next item in the list.
  while(d_pContextObjList != NULL) {
    d_pContextObjList = d_pContextObjList->restoreAndContinue();
  }
}

inline void
Scope::addToChain(ContextObj* pContextObj) throw(AssertionException) {
  if(d_pContextObjList != NULL) {
    d_pContextObjList->prev() = &pContextObj->next();
  }

  pContextObj->next() = d_pContextObjList;
  pContextObj->prev() = &d_pContextObjList;
  d_pContextObjList = pContextObj;
}

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CONTEXT_H */
