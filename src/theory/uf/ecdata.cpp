/*********************                                                        */
/** ecdata.cpp
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 **
 **/

#include "theory/uf/ecdata.h"

using namespace CVC4;
using namespace context;
using namespace theory;
using namespace uf;


ECData::ECData(Context * context, TNode n) :
  ContextObj(context),
  find(this),
  rep(n),
  watchListSize(0),
  first(NULL),
  last(NULL)
{}


bool ECData::isClassRep(){
  return this == this->find;
}

void ECData::addPredecessor(TNode n, Context* context){
  Assert(isClassRep());

  makeCurrent();

  Link * newPred = new (context->getCMM())  Link(context, n, first);
  first = newPred;
  if(last == NULL){
    last = newPred;
  }

  ++watchListSize;
}

ContextObj* ECData::save(ContextMemoryManager* pCMM) {
  return new(pCMM) ECData(*this);
}

void ECData::restore(ContextObj* pContextObj) {
  *this = *((ECData*)pContextObj);
}

Node ECData::getRep(){
  return rep;
}

unsigned ECData::getWatchListSize(){
  return watchListSize;
}


void ECData::setFind(ECData * ec){
  makeCurrent();
  find = ec;
}

ECData * ECData::getFind(){
  return find;
}


Link* ECData::getFirst(){
  return first;
}


void ECData::takeOverDescendantWatchList(ECData * nslave, ECData * nmaster){
  Assert(nslave != nmaster);
  Assert(nslave->getFind() == nmaster );

  nmaster->makeCurrent();

  nmaster->watchListSize +=  nslave->watchListSize;

  if(nmaster->first == NULL){
    nmaster->first = nslave->first;
    nmaster->last = nslave->last;
  }else if(nslave->first != NULL){
    Link * currLast = nmaster->last;
    currLast->next = nslave->first;
    nmaster->last = nslave->last;
  }
}
