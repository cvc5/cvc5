/******************************************************************************
 * Top contributors (to current version):
 *   Clark Barrett, Morgan Deters, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of base context operations.
 */

#include <iostream>
#include <string>
#include <vector>

#include "base/check.h"
#include "context/context.h"

namespace cvc5::context {

Context::Context() : d_pCNOpre(NULL), d_pCNOpost(NULL) {
  // Create new memory manager
  d_pCMM = new ContextMemoryManager();

  // Create initial Scope
  d_scopeList.push_back(new(d_pCMM) Scope(this, d_pCMM, 0));
}


Context::~Context() {
  // Delete all Scopes
  popto(0);

  // Delete the memory manager
  delete d_pCMM;

  // Clear ContextNotifyObj lists so there are no dangling pointers
  ContextNotifyObj* pCNO;
  while(d_pCNOpre != NULL) {
    pCNO = d_pCNOpre;
    pCNO->d_ppCNOprev = NULL;
    d_pCNOpre = pCNO->d_pCNOnext;
    pCNO->d_pCNOnext = NULL;
  }
  while(d_pCNOpost != NULL) {
    pCNO = d_pCNOpost;
    pCNO->d_ppCNOprev = NULL;
    d_pCNOpost = pCNO->d_pCNOnext;
    pCNO->d_pCNOnext = NULL;
  }
}

uint32_t Context::getLevel() const
{
  Assert(d_scopeList.size() > 0);
  return d_scopeList.size() - 1;
}

void Context::push() {
  Trace("pushpop") << std::string(2 * getLevel(), ' ') << "Push [to "
                   << getLevel() + 1 << "] { " << this << std::endl;

  // Create a new memory region
  d_pCMM->push();

  // Create a new top Scope
  d_scopeList.push_back(new(d_pCMM) Scope(this, d_pCMM, getLevel()+1));
}


void Context::pop() {
  Assert(getLevel() > 0) << "Cannot pop below level 0";

  // Notify the (pre-pop) ContextNotifyObj objects
  ContextNotifyObj* pCNO = d_pCNOpre;
  while(pCNO != NULL) {
    // pre-store the "next" pointer in case pCNO deletes itself on notify()
    ContextNotifyObj* next = pCNO->d_pCNOnext;
    pCNO->contextNotifyPop();
    pCNO = next;
  }

  // Grab the top Scope
  Scope* pScope = d_scopeList.back();

  // Restore the previous Scope
  d_scopeList.pop_back();

  // Restore all objects in the top Scope
  delete pScope;

  // Pop the memory region
  d_pCMM->pop();

  // Notify the (post-pop) ContextNotifyObj objects
  pCNO = d_pCNOpost;
  while(pCNO != NULL) {
    // pre-store the "next" pointer in case pCNO deletes itself on notify()
    ContextNotifyObj* next = pCNO->d_pCNOnext;
    pCNO->contextNotifyPop();
    pCNO = next;
  }

  Trace("pushpop") << std::string(2 * getLevel(), ' ') << "} Pop [to "
                   << getLevel() << "] " << this << std::endl;
}

void Context::popto(uint32_t toLevel)
{
  // Pop scopes until there are none left or toLevel is reached
  while (toLevel < getLevel()) pop();
}

void Context::addNotifyObjPre(ContextNotifyObj* pCNO) {
  // Insert pCNO at *front* of list
  if(d_pCNOpre != NULL)
    d_pCNOpre->prev() = &(pCNO->next());
  pCNO->next() = d_pCNOpre;
  pCNO->prev() = &d_pCNOpre;
  d_pCNOpre = pCNO;
}


void Context::addNotifyObjPost(ContextNotifyObj* pCNO) {
  // Insert pCNO at *front* of list
  if(d_pCNOpost != NULL)
    d_pCNOpost->prev() = &(pCNO->next());
  pCNO->next() = d_pCNOpost;
  pCNO->prev() = &d_pCNOpost;
  d_pCNOpost = pCNO;
}

void ContextObj::update()
{
  // Call save() to save the information in the current object
  ContextObj* pContextObjSaved = save(d_pScope->getCMM());

  // Check that base class data was saved
  Assert((pContextObjSaved->d_pContextObjNext == d_pContextObjNext
          && pContextObjSaved->d_ppContextObjPrev == d_ppContextObjPrev
          && pContextObjSaved->d_pContextObjRestore == d_pContextObjRestore
          && pContextObjSaved->d_pScope == d_pScope))
      << "save() did not properly copy information in base class";

  // Link the "saved" object in place of this ContextObj in the scope
  // we're moving it FROM.
  if(next() != NULL) {
    next()->prev() = &pContextObjSaved->next();
  }
  *prev() = pContextObjSaved;

  // Update Scope pointer to current top Scope
  d_pScope = d_pScope->getContext()->getTopScope();

  // Store the saved copy in the restore pointer
  d_pContextObjRestore = pContextObjSaved;

  // Insert object into the list of objects that need to be restored when this
  // Scope is popped.
  d_pScope->addToChain(this);
}

ContextObj* ContextObj::restoreAndContinue()
{
  // Variable to hold next object in list
  ContextObj* pContextObjNext;

  // Check the restore pointer.  If NULL, this must be the bottom Scope
  if(d_pContextObjRestore == NULL) {
    // might not be bottom scope, since objects allocated in context
    // memory don't get linked to scope 0
    //
    // Assert(d_pScope == d_pScope->getContext()->getBottomScope()) <<
    //        "Expected bottom scope";

    Trace("context") << "NULL restore object! " << this << std::endl;
    pContextObjNext = d_pContextObjNext;
    d_pScope = nullptr;

    // Nothing else to do
  } else {
    // Call restore to update the subclass data
    restore(d_pContextObjRestore);

    // Remember the next object in the list
    pContextObjNext = d_pContextObjNext;

    // Restore the base class data
    d_pScope = d_pContextObjRestore->d_pScope;
    next() = d_pContextObjRestore->d_pContextObjNext;
    prev() = d_pContextObjRestore->d_ppContextObjPrev;
    d_pContextObjRestore = d_pContextObjRestore->d_pContextObjRestore;

    // Re-link this ContextObj to the list in this scope
    if(next() != NULL) {
      next()->prev() = &next();
    }
    *prev() = this;
  }

  // Return the next object in the list
  return pContextObjNext;
}

void ContextObj::destroy()
{
  /* The object to destroy must be valid, i.e., its current state must belong
   * to a scope. We remove the object and its previous versions from their
   * respective scopes below. If this assertion is failing, you may have
   * created an object at a non-zero level and let it outlive the destruction
   * of that level. */
  Assert(d_pScope != nullptr);
  /* Context can be big and complicated, so we only want to process this output
   * if we're really going to use it. (Same goes below.) */
  Trace("context") << "before destroy " << this << " (level " << getLevel()
                   << "):" << std::endl << *getContext() << std::endl;

  for (;;)
  {
    // If valgrind reports invalid writes on the next few lines,
    // here's a hint: make sure all classes derived from ContextObj in
    // the system properly call destroy() in their destructors.
    // That's needed to maintain this linked list properly.
    if (next() != nullptr)
    {
      next()->prev() = prev();
    }
    *prev() = next();
    if (d_pContextObjRestore == nullptr)
    {
      break;
    }
    restoreAndContinue();
  }
  Trace("context") << "after destroy " << this << ":" << std::endl
                   << *getContext() << std::endl;
}


ContextObj::ContextObj(Context* pContext) :
  d_pScope(NULL),
  d_pContextObjRestore(NULL),
  d_pContextObjNext(NULL),
  d_ppContextObjPrev(NULL) {
  Assert(pContext != NULL) << "NULL context pointer";

  Trace("context") << "create new ContextObj(" << this << " inCMM=false)" << std::endl;
  d_pScope = pContext->getBottomScope();
  d_pScope->addToChain(this);
}

void ContextObj::enqueueToGarbageCollect() {
  Assert(d_pScope != NULL);
  d_pScope->enqueueToGarbageCollect(this);
}

ContextNotifyObj::ContextNotifyObj(Context* pContext, bool preNotify) {
  if(preNotify) {
    pContext->addNotifyObjPre(this);
  } else {
    pContext->addNotifyObjPost(this);
  }
}


ContextNotifyObj::~ContextNotifyObj() {
  if(d_pCNOnext != NULL) {
    d_pCNOnext->d_ppCNOprev = d_ppCNOprev;
  }
  if(d_ppCNOprev != NULL) {
    *d_ppCNOprev = d_pCNOnext;
  }
}

std::ostream& operator<<(std::ostream& out, const Context& context)
{
  static const std::string separator(79, '-');

  uint32_t level = context.d_scopeList.size() - 1;
  typedef std::vector<Scope*>::const_reverse_iterator const_reverse_iterator;
  for(const_reverse_iterator i = context.d_scopeList.rbegin();
      i != context.d_scopeList.rend();
      ++i, --level) {
    Scope* pScope = *i;
    Assert(pScope->getLevel() == level);
    Assert(pScope->getContext() == &context);
    out << separator << std::endl
        << *pScope << std::endl;
  }
  return out << separator << std::endl;
}

std::ostream& operator<<(std::ostream& out, const Scope& scope)
{
  out << "Scope " << scope.d_level << " [" << &scope << "]:";
  ContextObj* pContextObj = scope.d_pContextObjList;
  Assert(pContextObj == NULL
         || pContextObj->prev() == &scope.d_pContextObjList);
  while(pContextObj != NULL) {
    out << " <--> " << pContextObj;
    if(pContextObj->d_pScope != &scope) {
      out << " XXX bad scope" << std::endl;
    }
    Assert(pContextObj->d_pScope == &scope);
    Assert(pContextObj->next() == NULL
           || pContextObj->next()->prev() == &pContextObj->next());
    pContextObj = pContextObj->next();
  }
  return out << " --> NULL";
}

Scope::~Scope() {
  // Call restore() method on each ContextObj object in the list.
  // Note that it is the responsibility of restore() to return the
  // next item in the list.
  while (d_pContextObjList != NULL) {
    d_pContextObjList = d_pContextObjList->restoreAndContinue();
  }

  for (ContextObj* obj : d_garbage)
  {
    obj->deleteSelf();
  }
}

void Scope::enqueueToGarbageCollect(ContextObj* obj) {
  d_garbage.push_back(obj);
}

}  // namespace cvc5::context
