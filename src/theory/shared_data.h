/*********************                                                        */
/*! \file shared_data.h
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
 ** \brief Context-dependent data class for shared terms
 **
 ** Context-dependent data class for shared terms.
 ** Used by SharedTermManager.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__SHARED_DATA_H
#define __CVC4__THEORY__SHARED_DATA_H

#include "expr/node.h"
#include "context/context.h"
#include "context/cdo.h"
#include "context/context_mm.h"

namespace CVC4 {

namespace theory {
  class Theory;
}

/**
 * SharedData is the data for shared terms and is context dependent.
 *
 * SharedData maintains:
 * - list of theories sharing this term (as a bit-vector)
 * - size of the equivalence class (valid only if it is a find-representative)
 * - find pointer
 * - proof tree pointer (for explanations)
 * - equality associated with proof tree pointer
 * - theory associated with proof tree pointer
 * - the node associated with this data
 *
 * See also SharedAttr() in shared_term_manager.h
 */

class SharedData : public context::ContextObj {
private:
  /**
   * Bit-vector representation of list of theories needing to be notified if
   * this shared term is no longer the representative
   */
  uint64_t d_theories;

  /**
   * Size of this equivalence class
   */
  unsigned d_size;

  /**
   * Find pointer (standard union/find algorithm)
   */
  SharedData* d_find;

  /**
   * Pointer to next node (towards root) in proof forest
   */
  SharedData* d_proofNext;

  /**
   * In order to precisely reconstruct the equality that justifies this node
   * being equal to the node at d_proofNext, we need to know whether this edge
   * has been switched.  Value is meaningless at the proof root.
   */
  bool d_edgeReversed;

  /**
   * The theory that can explain the equality of this node and the node at
   * d_proofNext.  Not valid if this is proof root.
   */
  theory::Theory* d_explainingTheory;

  /**
   * This is a pointer back to the node associated with this SharedData object.
   *
   * The following invariant should be maintained:
   *  (n.getAttribute(SharedAttr()))->d_rep == n
   * i.e. rep is equal to the node that maps to the SharedData using SharedAttr.
   *
   */
  TNode d_rep;

  /** Context-dependent operation: save this SharedData */
  context::ContextObj* save(context::ContextMemoryManager* pCMM);

  /** Context-dependent operation: restore this SharedData */
  void restore(context::ContextObj* pContextObj);

public:
  /**
   * Creates a SharedData object with the representative n
   */
  SharedData(context::Context* context, TNode n, uint64_t theories);

  /** Destructor for SharedDatas */
  ~SharedData() {
    destroy();
  }

  /**
   * Get list of theories for this shared term
   */
  uint64_t getTheories() const { return d_theories; }

  /**
   * Set list of theories for this shared term
   */
  void setTheories(uint64_t t) { makeCurrent(); d_theories = t; }

  /**
   * Get size of equivalence class (valid if getFind() == this)
   */
  unsigned getSize() const { return d_size; }

  /**
   * Set size of equivalence class
   */

  void setSize(unsigned size) { makeCurrent(); d_size = size; }

  /**
   * Returns the find pointer of the SharedData.
   * If this is the representative of the equivalence class, then getFind() == this
   */
  SharedData* getFind() const { return d_find; }

  /**
   * Sets the find pointer
   */
  void setFind(SharedData * pData) { makeCurrent(); d_find = pData; }

  /**
   * Return true iff this is the root of the proof tree
   */
  bool isProofRoot() const { return d_proofNext == this; }

  /**
   * Get the next link in the proof tree
   */
  SharedData* getProofNext() const { return d_proofNext; }

  /**
   * Set the next link in the proof tree
   */
  void setProofNext(SharedData* pData) { makeCurrent(); d_proofNext = pData; }

  /**
   * Get the edge reversed property of this node
   */
  bool getEdgeReversed() const { return d_edgeReversed; }

  /**
   * Set the edge reversed flag to value
   */
  void setEdgeReversed(bool value) { makeCurrent(); d_edgeReversed = value; }

  /**
   * Get the original equality that created the link from this node to the next
   * proof node.
   */
  Node getEquality() const {
    return d_edgeReversed
      ? NodeManager::currentNM()->mkNode(kind::EQUAL, d_proofNext->getRep(), d_rep)
      : NodeManager::currentNM()->mkNode(kind::EQUAL, d_rep, d_proofNext->getRep());
  }

  /**
   * Get the explaining theory
   */
  theory::Theory* getExplainingTheory() const { return d_explainingTheory; }

  /**
   * Set the explaining theory
   */
  void setExplainingTheory(theory::Theory* t) { makeCurrent(); d_explainingTheory = t; }

  /**
   * Get the shared term associated with this data
   */
  Node getRep() const { return d_rep; }

  /**
   * Reverse the edges in the proof tree from here to the root.
   */
  void reverseEdges();

};/* class SharedData */

}/* CVC4 namespace */

#endif /* __CVC4__THEORY__SHARED_DATA_H */
