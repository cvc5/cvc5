/*********************                                                        */
/*! \file shared_term_manager.h
 ** \verbatim
 ** Original author: barrett
 ** Major contributors: 
 ** Minor contributors (to current version): 
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Manager for shared terms
 **
 ** Manager for shared terms.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SHARED_TERM_MANAGER_H
#define __CVC4__SHARED_TERM_MANAGER_H

#include "expr/node.h"
#include "theory/shared_data.h"

namespace CVC4 {

namespace context {
  class Context;
}

namespace theory {
  class Theory;
}

/**
 * Manages shared terms
 */
class SharedTermManager {

  TheoryEngine* d_engine;

  context::Context* d_context;

  std::vector<theory::Theory*> d_theories;

  SharedData* find(SharedData* pData);

public:
  SharedTermManager(TheoryEngine* engine, context::Context* context);

  void registerTheory(theory::Theory* th);

  void addTerm(TNode n, theory::Theory* parent,
               theory::Theory* child);

  void addEq(theory::Theory* thReason, TNode eq);

  Node explain(TNode eq);

};/* class SharedTermManager */

/**
 * Cleanup function for SharedData. This will be called whenever
 * a SharedAttr is being destructed.
 */
struct SharedDataCleanupStrategy {
  static void cleanup(SharedData* sd) {
    sd->deleteSelf();
  }
};/* struct SharedDataCleanupStrategy */

/** Unique name to use for constructing ECAttr. */
struct SharedAttrTag {};

/**
 * SharedAttr is the attribute that maps a node to its SharedData.
 */
typedef expr::Attribute<SharedAttrTag, SharedData*,
                        SharedDataCleanupStrategy> SharedAttr;


}/* CVC4 namespace */

#endif /* __CVC4__SHARED_TERM_MANAGER_H */
