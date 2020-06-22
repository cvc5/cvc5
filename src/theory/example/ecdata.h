/*********************                                                        */
/*! \file ecdata.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Morgan Deters, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Context dependent equivalence class datastructure for nodes.
 **
 ** Context dependent equivalence class datastructure for nodes.
 ** Currently keeps a context dependent watch list.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__TIM__ECDATA_H
#define CVC4__THEORY__UF__TIM__ECDATA_H

#include "expr/node.h"
#include "context/context.h"
#include "context/cdo.h"
#include "context/context_mm.h"

namespace CVC4 {
namespace theory {
namespace uf {
namespace tim {

/**
 * Link is a context dependent linked list of nodes.
 * Link is intended to be allocated in a Context's memory manager.
 * The next pointer of the list is context dependent, but the node being
 * pointed to is fixed for the life of the Link.
 *
 * Clients of Link are intended not to modify the node that is being pointed
 * to in good faith.  This may change in the future.
 */
struct Link {
  /**
   * Pointer to the next element in linked list.
   * This is context dependent. 
   */
  context::CDO<Link*> d_next;

  /**
   * Link is supposed to be allocated in a region of a
   * ContextMemoryManager.  In order to avoid having to decrement the
   * ref count at deletion time, it is preferrable for the user of
   * Link to maintain the invariant that data will survival for the
   * entire scope of the TNode.
   */
  TNode d_data;

  /**
   * Creates a new Link w.r.t. a context for the node n.
   * An optional parameter is to specify the next element in the link.
   */
  Link(context::Context* context, TNode n, Link* l = NULL) :
    d_next(true, context, l),
    d_data(n) {
    Debug("context") << "Link: " << this
                     << " so cdo is " << &d_next << std::endl;
  }

  /**
   * Allocates a new Link in the region for the provided ContextMemoryManager.
   * This allows for cheap cleanup on pop.
   */
  static void* operator new(size_t size, context::ContextMemoryManager* pCMM) {
    return pCMM->newData(size);
  }

 private:
  /**
   * The destructor isn't actually defined.  This declaration keeps
   * the compiler from creating (wastefully) a default definition, and
   * ensures that we get a link error if someone uses Link in a way
   * that requires destruction.  Objects of class Link should always
   * be allocated in a ContextMemoryManager, which doesn't call
   * destructors.
   */
  ~Link();

  /**
   * Just like the destructor, this is not defined.  This ensures no
   * one tries to create a Link on the heap.
   */
  static void* operator new(size_t size);

};/* struct Link */


/**
 * ECData is a equivalence class object that is context dependent.
 * It is developed in order to support the congruence closure algorithm
 * in TheoryUF, and is not intended to be used outside of that package.
 *
 * ECData maintains:
 * - find pointer for the equivalence class (disjoint set forest)
 * - the node that represents the equivalence class.
 * - maintains a predecessorlist/watchlist
 *
 * ECData does not have support for the canonical find and union operators
 * for disjoint set forests.  Instead it only provides access to the find
 * pointer. The implementation of find is ccFind in TheoryUF.
 * union is broken into 2 phases:
 *  1) setting the find point with setFind
 *  2) taking over the watch list of the other node.
 * This is a technical requirement for the implementation of TheoryUF.
 * (See ccUnion in TheoryUF for more information.)
 *
 * The intended paradigm for iterating over the watch list of ec is:
 *      for(Link* i = ec->getFirst(); i != NULL; i = i->next );
 *
 * See also ECAttr() in theory_uf.h, and theory_uf.cpp where the codde that uses
 * ECData lives.
 */
class ECData : public context::ContextObj {
private:
  /**
   * This is the standard disjoint set forest find pointer.
   *
   * Why an ECData pointer instead of a node?
   * This was chosen to be a ECData pointer in order to shortcut at least one
   * table every time the find pointer is examined.
   */
  ECData* d_find;

  /**
   * This is pointer back to the node that represents this equivalence class.
   *
   * The following invariant should be maintained:
   *  (n.getAttribute(ECAttr()))->rep == n
   * i.e. rep is equal to the node that maps to the ECData using ECAttr.
   *
   * Tricky part: This needs to be a TNode, not a Node.
   * Suppose that rep were a hard link.
   * When a node n maps to an ECData via the ECAttr() there will be a hard
   * link back to n in the ECData. The attribute does not do garbage collection
   * until the node gets garbage collected, which does not happen until its
   * ref count drops to 0. So because of this cycle neither the node and
   * the ECData will never get garbage collected.
   * So this needs to be a soft link.
   */
  TNode d_rep;

  // Watch list data structures follow

  /**
   * Maintains watch list size for more efficient merging.
   */
  unsigned d_watchListSize;

  /**
   * Pointer to the beginning of the watchlist.
   * This value is NULL iff the watch list is empty.
   */
  Link* d_first;

  /**
   * Pointer to the end of the watch-list.
   * This is maintained in order to constant time list merging.
   * (This does not give any asymptotic improve as this is currently always
   * preceeded by an O(|watchlist|) operation.)
   * This value is NULL iff the watch list is empty.
   */
  Link* d_last;

  /** Context-dependent operation: save this ECData */
  context::ContextObj* save(context::ContextMemoryManager* pCMM);

  /** Context-dependent operation: restore this ECData */
  void restore(context::ContextObj* pContextObj);

public:
  /**
   * Returns true if this ECData object is the current representative of
   * the equivalence class.
   */
  bool isClassRep();

  /**
   * Adds a node to the watch list of the equivalence class.  Does
   * context-dependent memory allocation in the Context with which
   * this ECData was created.
   *
   * @param n the node to be added.
   * @pre isClassRep() == true
   */
  void addPredecessor(TNode n);

  /**
   * Creates a EQ with the representative n
   * @param context the context to associate with this ecdata.
   *   This is required as ECData is context dependent
   * @param n the node that corresponds to this ECData
   */
  ECData(context::Context* context, TNode n);

  /** Destructor for ECDatas */
  ~ECData() {
    Debug("ufgc") << "Calling ECData destructor" << std::endl;
    destroy();
  }

  /**
   * An ECData takes over the watch list of another ECData.
   * This is the second step in the union operator for ECData.
   * This should be called after nslave->setFind(nmaster);
   * After this is done nslave's watch list should never be accessed by
   * getLast() or getFirst()
   */
  static void takeOverDescendantWatchList(ECData * nslave, ECData * nmaster);

  /**
   * Returns the representative of this ECData.
   */
  Node getRep();

  /**
   * Returns the size of the equivalence class.
   */
  unsigned getWatchListSize();

  /**
   * Returns a pointer the first member of the watch list.
   */
  Link* getFirst();


  /**
   * Returns the find pointer of the ECData.
   * If isClassRep(), then getFind() == this
   */
  ECData* getFind();

  /**
   * Sets the find pointer of the equivalence class to be another ECData object.
   *
   * @pre isClassRep() == true
   * @pre ec->isClassRep() == true
   * @post isClassRep() == false
   * @post ec->isClassRep() == true
   */
  void setFind(ECData * ec);

};/* class ECData */

}/* CVC4::theory::uf::tim namespace */
}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__UF__TIM__ECDATA_H */
