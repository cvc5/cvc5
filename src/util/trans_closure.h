/*********************                                                        */
/*! \file trans_closure.h
 ** \verbatim
 ** Original author: Clark Barrett
 ** Major contributors: Andrew Reynolds
 ** Minor contributors (to current version): Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The transitive closure module
 **
 ** The transitive closure module.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UTIL__TRANSITIVE_CLOSURE_H
#define __CVC4__UTIL__TRANSITIVE_CLOSURE_H

#include "context/context.h"
#include "expr/node.h"
#include <map>

#include "context/cdlist.h"
#include "context/cdhashmap.h"
#include "context/cdo.h"

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
  void clear() { d_data = 0; if( d_next ) d_next->clear(); }
  bool read(unsigned index) {
    if (index < 64) return (d_data & (uint64_t(1) << index)) != 0;
    else if (d_next == NULL) return false;
    else return d_next->read(index - 64);
  }

  void write(unsigned index) {
    if (index < 64) {
      uint64_t mask = uint64_t(1) << index;
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
  context::CDO<unsigned> adjIndex;

public:
  TransitiveClosure(context::Context* context) : d_context(context), adjIndex(context,0) {}
  virtual ~TransitiveClosure();

  /* Add an edge from node i to node j.  Return false if successful, true if this edge would create a cycle */
  bool addEdge(unsigned i, unsigned j);
  /** whether node i is connected to node j */
  bool isConnected(unsigned i, unsigned j);
  void debugPrintMatrix();
};

/**
 * Transitive closure module for nodes in CVC4.
 *
 */
class TransitiveClosureNode : public TransitiveClosure{
  context::CDO< unsigned > d_counter;
  context::CDHashMap< Node, unsigned, NodeHashFunction > nodeMap;
  //for debugging
  context::CDList< std::pair< Node, Node > > currEdges;
public:
  TransitiveClosureNode(context::Context* context) :
    TransitiveClosure(context), d_counter( context, 0 ), nodeMap( context ), currEdges(context) {}
  ~TransitiveClosureNode(){}

  /** get id for node */
  unsigned getId( Node i );
  /** Add an edge from node i to node j.  Return false if successful, true if this edge would create a cycle */
  bool addEdgeNode(Node i, Node j) {
    currEdges.push_back( std::pair< Node, Node >( i, j ) );
    return addEdge( getId( i ), getId( j ) );
  }
  /** whether node i is connected to node j */
  bool isConnectedNode(Node i, Node j) {
    return isConnected( getId( i ), getId( j ) );
  }
  void debugPrint();
};

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__TRANSITIVE_CLOSURE_H */
