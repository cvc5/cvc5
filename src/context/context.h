/*********************                                           -*- C++ -*-  */
/** context.h
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009 The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Context class and context manager.
 **/

#ifndef __CVC4__CONTEXT__CONTEXT_H
#define __CVC4__CONTEXT__CONTEXT_H

#include "context/context_mm.h"

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
   * Pointer to the current (top) Scope for this Context.
   */
  Scope* d_pScopeTop;

  /**
   * Pointer to the initial (bottom) Scope for this Context.
   */
  Scope* d_pScopeBottom;

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
  Scope* getTopScope() const { return d_pScopeTop; }

  /**
   * Return the initial (bottom) scope
   */
  Scope* getBottomScope() const { return d_pScopeBottom; }

  /**
   * Return the current Scope level.  Implemented as inline function following
   * declaration of Scope class.
   */
  int getLevel() const;

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
   * Previous Scope in this context
   */
  Scope* d_pScopePrev;

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
  Scope(Context* pContext, ContextMemoryManager* pCMM,
        Scope* pScopePrev = NULL)
    : d_pContext(pContext), d_pCMM(pCMM), d_pScopePrev(pScopePrev),
      d_level(0), d_pContextObjList(NULL)
    { if (pScopePrev != NULL) d_level = pScopePrev->getLevel() + 1; }

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
   * Get the pointer to the previous Scope (should be NULL if no previous
   * scope).
   */
  Scope* getScopePrev() const { return d_pScopePrev; }

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
  void* operator new(size_t size, ContextMemoryManager* pCMM)
    { return pCMM->newData(size); }

  /**
   * Overload operator delete for Scope objects allocated using
   * ContextMemoryManager.  No need to do anything because memory is freed
   * automatically when the ContextMemoryManager pop() method is called.
   */
  void operator delete(void* pMem) {}

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
   *    ContextMemoryManager, it should be freed when restore() is called.
   * 3. Implement restore()
   *    The role of restore() is, given the ContextObj returned by a previous
   *    call to save(), to restore the current object to the state it was in
   *    when save() was called.  Note that the implementation of restore does
   *    *not* need to worry about restoring the base class data.  This is done
   *    automatically.  restore() should not have to free any memory as any
   *    memory allocated by save() should have been done using the
   *    ContextMemoryManager (see item 2 above).
   * 4. In the subclass implementation, any time the state is about to be
   *    changed, first call to makeCurrent().
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

public:
  /**
   * Create a new ContextObj.  The initial scope is set to the bottom
   * scope of the Context.
   */
  ContextObj(Context* context);

  /**
   * Destructor: Calls restore until restored to initial version.  Also removes
   * object from all Scope lists.  Note that this doesn't actually free the
   * memory allocated by the ContextMemoryManager for this object.  This isn't
   * done until the corresponding Scope is popped.
   */
  virtual ~ContextObj();

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

inline int Context::getLevel() const { return getTopScope()->getLevel(); }

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

template <class T>
class CDO;

template <class T>
class CDMap;

template <class T>
class CDList;

template <class T>
class CDSet;

}/* CVC4::context namespace */
}/* CVC4 namespace */

#endif /* __CVC4__CONTEXT__CONTEXT_H */

