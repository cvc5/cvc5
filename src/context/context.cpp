/*********************                                                        */
/** context.cpp
 ** Original author: mdeters
 ** Major contributors: barrett
 ** Minor contributors (to current version): dejan
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **/


#include "context/context.h"
#include "util/Assert.h"

namespace CVC4 {
namespace context {


Context::Context() : d_pCNOpre(NULL), d_pCNOpost(NULL) {
  // Create new memory manager
  d_pCMM = new ContextMemoryManager();

  // Create initial Scope
  d_scopeList.push_back(new(d_pCMM) Scope(this, d_pCMM, 0));
}


Context::~Context() throw(AssertionException) {
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


void Context::push() {
  // FIXME: TRACE("pushpop", indentStr, "Push", " {");

  // Create a new memory region
  d_pCMM->push();

  // Create a new top Scope
  d_scopeList.push_back(new(d_pCMM) Scope(this, d_pCMM, getLevel()+1));
}


void Context::pop() {
  Assert(getLevel() > 0, "Cannot pop below level 0");

  // Notify the (pre-pop) ContextNotifyObj objects
  ContextNotifyObj* pCNO = d_pCNOpre;
  while(pCNO != NULL) {
    pCNO->notify();
    pCNO = pCNO->d_pCNOnext;
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
    pCNO->notify();
    pCNO = pCNO->d_pCNOnext;
  }

  //FIXME:  TRACE("pushpop", indentStr, "}", " Pop");
}


void Context::popto(int toLevel) {
  // Pop scopes until there are none left or toLevel is reached
  if(toLevel < 0) toLevel = 0;
  while(toLevel < getLevel()) pop();
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


void ContextObj::update() {
  // Call save() to save the information in the current object
  ContextObj* pContextObjSaved = save(d_pScope->getCMM());

  // Check that base class data was saved
  Assert(pContextObjSaved->d_pContextObjNext == d_pContextObjNext &&
         pContextObjSaved->d_ppContextObjPrev == d_ppContextObjPrev &&
         pContextObjSaved->d_pContextObjRestore == d_pContextObjRestore &&
         pContextObjSaved->d_pScope == d_pScope,
         "save() did not properly copy information in base class");

  // Update Scope pointer to current top Scope
  d_pScope = d_pScope->getContext()->getTopScope();

  // Store the saved copy in the restore pointer
  d_pContextObjRestore = pContextObjSaved;

  // Insert object into the list of objects that need to be restored when this
  // Scope is popped.
  d_pScope->addToChain(this);
}


ContextObj* ContextObj::restoreAndContinue() {
  // Variable to hold next object in list
  ContextObj* pContextObjNext;

  // Check the restore pointer.  If NULL, this must be the bottom Scope
  if(d_pContextObjRestore == NULL) {
    Assert(d_pScope == d_pScope->getContext()->getBottomScope(),
           "Expected bottom scope");
    pContextObjNext = d_pContextObjNext;
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
  }
  // Return the next object in the list
  return pContextObjNext;
}


ContextObj::ContextObj(Context* pContext) :
  d_pContextObjRestore(NULL) {

  Assert(pContext != NULL, "NULL context pointer");

  d_pScope = pContext->getBottomScope();
  d_pScope->addToChain(this);
}


ContextObj::~ContextObj() throw(AssertionException) {
  for(;;) {
    if(next() != NULL) {
      next()->prev() = prev();
    }
    *(prev()) = next();
    if(d_pContextObjRestore == NULL) {
      break;
    }
    restoreAndContinue();
  }
}


ContextNotifyObj::ContextNotifyObj(Context* pContext, bool preNotify) {
  if(preNotify) {
    pContext->addNotifyObjPre(this);
  } else {
    pContext->addNotifyObjPost(this);
  }
}


ContextNotifyObj::~ContextNotifyObj() throw(AssertionException) {
  if(d_pCNOnext != NULL) {
    d_pCNOnext->d_ppCNOprev = d_ppCNOprev;
  }
  if(d_ppCNOprev != NULL) {
    *(d_ppCNOprev) = d_pCNOnext;
  }
}


} /* CVC4::context namespace */
} /* CVC4 namespace */
