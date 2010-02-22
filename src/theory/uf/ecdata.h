/*********************                                                        */
/** ecdata.h
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
 ** Context dependent equivalence class datastructure for nodes.
 ** Currently keeps a context dependent watch list.
 **/

#ifndef __CVC4__THEORY__UF__ECDATA_H
#define __CVC4__THEORY__UF__ECDATA_H

#include "expr/node.h"
#include "context/context.h"
#include "context/context_mm.h"

namespace CVC4 {
namespace theory {

struct Link {
  context::CDO< Link* > next;
  
  //TODO soft reference
  Node data;
  
  Link(context::Context* context, Node n, Link * l = NULL):
    next(context, l), data(n)
  {}

  static void* operator new(size_t size, context::ContextMemoryManager* pCMM) {
    return pCMM->newData(size);
  }
  
};



class ECData : public context::ContextObj {
private:
  ECData * find;

  Node rep;
  
  unsigned watchListSize;
  Link * first;
  Link * last;


  context::ContextObj* save(context::ContextMemoryManager* pCMM);
  void restore(context::ContextObj* pContextObj);


public:
  /**
   * Returns true if this ECData object is the current representative of
   * the equivalence class.
   */
  bool isClassRep();

  /**
   * Adds a node to the watch list of the equivalence class.
   * Requires a context to do memory management.
   * @param n the node to be added.
   * @pre isClassRep() == true
   */
  void addPredecessor(Node n, context::Context* context);
  


  /**
   * Creates a EQ with the representative n
   * @param context the context to associate with this ecdata.
   *   This is required as ECData is context dependent
   * @param n the node that corresponds to this ECData
   */
  ECData(context::Context* context, const Node & n);
  
  static void takeOverDescendantWatchList(ECData * nslave, ECData * nmaster);

  static ECData * ccFind(ECData * fp);


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
   * @pre isClassRep() == true
   * @pre ec->isClassRep() == true
   * @post isClassRep() == false
   * @post ec->isClassRep() == true
   */
  void setFind(ECData * ec);
  
private:

  
  /**
   * @pre isClassRep() == true
   */
  void setWatchListSize(unsigned newSize);

  /**
   * @pre isClassRep() == true
   */
  void setFirst(Link * nfirst);

  Link* getLast();

  /**
   * @pre isClassRep() == true
   */
  void setLast(Link * nlast);
  
}; /* class ECData */

}/* CVC4::theory namespace */
}/* CVC4 namespace */


#endif /* __CVC4__THEORY__UF__ECDATA_H */
