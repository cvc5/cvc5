/*********************                                                        */
/** ecdata.cpp
 ** Original author: taking
 ** Major contributors: mdeters
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
  d_find(this),
  d_rep(n),
  d_watchListSize(0),
  d_first(NULL),
  d_last(NULL)
{}


bool ECData::isClassRep(){
  return this == this->d_find;
}

void ECData::addPredecessor(TNode n, Context* context){
  Assert(isClassRep());

  makeCurrent();

  Link * newPred = new (context->getCMM())  Link(context, n, d_first);
  d_first = newPred;
  if(d_last == NULL){
    d_last = newPred;
  }

  ++d_watchListSize;
}

ContextObj* ECData::save(ContextMemoryManager* pCMM) {
  return new(pCMM) ECData(*this);
}

void ECData::restore(ContextObj* pContextObj) {
  ECData* data = (ECData*)pContextObj;
  d_find = data->d_find;
  d_first = data->d_first;
  d_last = data->d_last;
  d_rep = data->d_rep;
  d_watchListSize = data->d_watchListSize;
}

Node ECData::getRep(){
  return d_rep;
}

unsigned ECData::getWatchListSize(){
  return d_watchListSize;
}


void ECData::setFind(ECData * ec){
  makeCurrent();
  d_find = ec;
}

ECData * ECData::getFind(){
  return d_find;
}


Link* ECData::getFirst(){
  return d_first;
}


void ECData::takeOverDescendantWatchList(ECData * nslave, ECData * nmaster){
  Assert(nslave != nmaster);
  Assert(nslave->getFind() == nmaster );

  nmaster->makeCurrent();

  nmaster->d_watchListSize +=  nslave->d_watchListSize;

  if(nmaster->d_first == NULL){
    nmaster->d_first = nslave->d_first;
    nmaster->d_last = nslave->d_last;
  }else if(nslave->d_first != NULL){
    Link * currLast = nmaster->d_last;
    currLast->d_next = nslave->d_first;
    nmaster->d_last = nslave->d_last;
  }
}
