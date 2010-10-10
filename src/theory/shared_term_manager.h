/*********************                                                        */
/*! \file shared_term_manager.h
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
 ** \brief Manager for shared terms
 **
 ** Manager for shared terms.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__SHARED_TERM_MANAGER_H
#define __CVC4__SHARED_TERM_MANAGER_H

#include <set>
#include <vector>

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

  /**
   * Pointer back to theory engine
   */
  TheoryEngine* d_engine;

  /**
   * Pointer to context
   */
  context::Context* d_context;

  /**
   * List of all theories indexed by theory id (built by calls to
   * registerTheory())
   */
  std::vector<theory::Theory*> d_theories;

  /**
   * Private method to find equivalence class representative in
   * union-find data structure.
   */
  SharedData* find(SharedData* pData) const;

  /**
   * Helper function for explain: add all reasons for equality at
   * pData to set s
   */
  void collectExplanations(SharedData* pData, std::set<Node>& s) const;

public:
  /**
   * Constructor
   */
  SharedTermManager(TheoryEngine* engine, context::Context* context);

  /**
   * Should be called once for each theory at setup time
   */
  void registerTheory(theory::Theory* th);

  /**
   * Called by theory engine to indicate that node n is shared by
   * theories parent and child.
   */
  void addTerm(TNode n, theory::Theory* parent,
               theory::Theory* child);

  /**
   * Called by theory engine or theories to notify the shared term
   * manager that two terms are equal.
   *
   * @param eq the equality between shared terms
   * @param thReason the theory that knows why, NULL means it's a SAT
   * assertion
   */
  void addEq(TNode eq, theory::Theory* thReason = NULL);

  /**
   * Called by theory engine or theories to notify the shared term
   * manager that two terms are disequal.
   *
   * @param eq the equality between shared terms whose negation now
   * holds
   * @param thReason the theory that knows why, NULL means it's a SAT
   * assertion
   */
  void addDiseq(TNode eq, theory::Theory* thReason = NULL) { }

  /**
   * Get an explanation for an equality known by the SharedTermManager
   */
  Node explain(TNode eq) const;

  /**
   * Get the representative node in the equivalence class containing n
   */
  Node getRep(TNode n) const;

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
