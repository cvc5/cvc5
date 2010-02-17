#include "theory/uf/ecdata.h"

using namespace CVC4;
using namespace context;
using namespace theory;


ECData::ECData(Context * context, const Node & n) :
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

void ECData::addPredecessor(Node n, Context* context){
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

void ECData::setWatchListSize(unsigned newSize){
  Assert(isClassRep());

  makeCurrent();
  watchListSize = newSize;
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


Link* ECData::getLast(){
  return last;
}

void ECData::setFirst(Link * nfirst){
  makeCurrent();
  first = nfirst;
}

void ECData::setLast(Link * nlast){
  makeCurrent();
  last = nlast;
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
