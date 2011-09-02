/*********************                                                        */
/*! \file shared_data.cpp
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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
  d_edgeReversed(false),
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
  d_edgeReversed = data->d_edgeReversed;
  d_explainingTheory = data->d_explainingTheory;
  d_rep = data->d_rep;
}


void SharedData::reverseEdges() {
  Assert(!isProofRoot(), "reverseEdges called on proof root");

  SharedData* parent = this;
  SharedData* current = d_proofNext;
  bool reversed = d_edgeReversed;
  Theory* explainingTheory = d_explainingTheory;

  makeCurrent();

  // Make this the proof root
  d_proofNext = this;
  
  // Reverse the edges from here to the former root
  bool tmpReversed;
  Theory* tmpTheory;
  SharedData* tmpData;

  while (!current->isProofRoot()) {
    tmpReversed = current->getEdgeReversed();
    current->setEdgeReversed(!reversed);
    reversed = tmpReversed;

    tmpTheory = current->getExplainingTheory();
    current->setExplainingTheory(explainingTheory);
    explainingTheory = tmpTheory;

    tmpData = current->getProofNext();
    current->setProofNext(parent);
    parent = current;
    current = tmpData;
  }
  current->setEdgeReversed(!reversed);
  current->setExplainingTheory(explainingTheory);
  current->setProofNext(parent);
}
