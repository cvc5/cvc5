/*********************                                                        */
/*! \file shared_data.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Implementation of shared data for shared term manager.
 **
 ** Implementation of shared data used by the shared term manager.  This is a
 ** context-dependent object.
 **/


#include "theory/shared_data.h"
#include "theory/theory.h"


using namespace CVC4;
using namespace context;
using namespace theory;


SharedData::SharedData(Context * context, TNode n, uint64_t theories) :
  ContextObj(context),
  d_theories(theories),
  d_size(1),
  d_find(this),
  d_proofNext(this),
  d_explainingTheory(NULL),
  d_rep(n) {
}


ContextObj* SharedData::save(ContextMemoryManager* pCMM) {
  return new(pCMM) SharedData(*this);
}


void SharedData::restore(ContextObj* pContextObj) {
  SharedData* data = (SharedData*)pContextObj;
  d_theories = data->d_theories;
  d_size = data->d_size;
  d_find = data->d_find;
  d_proofNext = data->d_proofNext;
  d_equality = data->d_equality;
  d_explainingTheory = data->d_explainingTheory;
  d_rep = data->d_rep;
}


void SharedData::reverseEdges() {
  Assert(!isProofRoot(), "reverseEdges called on proof root");

  SharedData* parent = this;
  SharedData* current = d_proofNext;
  Node equality = d_equality;
  Theory* explainingTheory = d_explainingTheory;

  makeCurrent();
  d_proofNext = this;
  
  Node tmpNode;
  Theory* tmpTheory;
  SharedData* tmpData;

  while (!current->isProofRoot()) {
    tmpNode = current->getEquality();
    current->setEquality(equality);
    equality = tmpNode;

    tmpTheory = current->getExplainingTheory();
    current->setExplainingTheory(explainingTheory);
    explainingTheory = tmpTheory;

    tmpData = current->getProofNext();
    current->setProofNext(parent);
    parent = current;
    current = tmpData;
  }
  current->setEquality(equality);
  current->setExplainingTheory(explainingTheory);
  current->setProofNext(parent);
}
