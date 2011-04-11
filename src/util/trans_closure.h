/*********************                                                        */
/*! \file transitive_closure.h
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
 ** \brief The transitive closure module
 **
 ** The transitive closure module.
 **/

#ifndef __CVC4__UTIL__TRANSITIVE_CLOSURE_H
#define __CVC4__UTIL__TRANSITIVE_CLOSURE_H

#include "context/context.h"

namespace CVC4 {

/*
 * Implements context-dependent variable-sized boolean vector
 */
class CDBV :public context::ContextObj {
  uint64_t d_data;
  CDBV* d_next;

  CDBV(const CDBV& cdbv) : ContextObj(cdbv), d_data(cdbv.d_data), d_next(cdbv.d_next) {}

  /**
   * operator= for CDBV is private to ensure CDBV object is not copied.
   */
  CDBV& operator=(const CDBV& cdbv);

protected:
  context::ContextObj* save(context::ContextMemoryManager* pCMM) {
    return new(pCMM) CDBV(*this);
  }

  void restore(context::ContextObj* pContextObj) {
    d_data = ((CDBV*) pContextObj)->d_data;
  }

  uint64_t data() { return d_data; }

  CDBV* next() { return d_next; }

public:
  CDBV(context::Context* context) : 
    ContextObj(context), d_data(0), d_next(NULL)
  {}

  ~CDBV() { 
    if (d_next != NULL) {
      d_next->deleteSelf();
    }
    destroy();
  }

  bool read(unsigned index) {
    if (index < 64) return (d_data & (unsigned(1) << index)) != 0;
    else if (d_next == NULL) return false;
    else return d_next->read(index - 64);
  }

  void write(unsigned index) {
    if (index < 64) {
      unsigned mask = unsigned(1) << index;
      if ((d_data & mask) != 0) return;
      makeCurrent();
      d_data = d_data | mask;
    }
    else if (d_next != NULL) {
      d_next->write(index - 64);
    }
    else {
      makeCurrent();
      d_next = new(true) CDBV(getContext());
      d_next->write(index - 64);
    }      
  }

  void merge(CDBV* pcdbv) {
    d_data = d_data | pcdbv->data();
    if (d_next != NULL && pcdbv->next() != NULL) {
      d_next->merge(pcdbv->next());
    }
  }

};


/**
 * Transitive closure module for CVC4.
 *
 */
class TransitiveClosure {
  context::Context* d_context;
  std::vector<CDBV* > adjMatrix;

public:
  TransitiveClosure(context::Context* context) : d_context(context) {}
  ~TransitiveClosure();

  /* Add an edge from node i to node j.  Return false if successful, true if this edge would create a cycle */
  bool addEdge(unsigned i, unsigned j);
  void debugPrintMatrix();
};

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__TRANSITIVE_CLOSURE_H */
