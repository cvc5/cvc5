/*********************                                                        */
/*! \file congruence_closure.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief The congruence closure module
 **
 ** The congruence closure module.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__UTIL__CONGRUENCE_CLOSURE_H
#define __CVC4__UTIL__CONGRUENCE_CLOSURE_H

#include <list>
#include <algorithm>
#include <utility>
#include <ext/hash_map>

#include "expr/node_manager.h"
#include "expr/node.h"
#include "context/cdmap.h"

namespace CVC4 {

/**
 * Congruence closure module for CVC4.
 *
 * This is a service class for theories.  One uses a CongruenceClosure
 * by adding a number of relevant terms with addTerm() and equalities
 * with addEquality().  It then gets notified (through OutputChannel,
 * below), of new equalities.
 *
 * OutputChannel is a template argument (it's probably a thin layer,
 * and we want to avoid a virtual call hierarchy in this case, and
 * enable aggressive inlining).  It need only implement one method,
 * merge():
 *
 *   class MyOutputChannel {
 *   public:
 *     void merge(TNode a, TNode b) {
 *       // CongruenceClosure is notifying us that "a" is now the EC
 *       // representative for "b" in this context.  After a pop, "a"
 *       // will be its own representative again.  Note that "a" and
 *       // "b" might never have been added with addTerm().  However,
 *       // something in their equivalence class was (for which a
 *       // previous merge() would have notified you of their EC
 *       // representative, which is now "a" or "b").
 *       //
 *       // This call is made immediately after the merge is done, and
 *       // while other pending merges may be on the queue.  In particular,
 *       // any exception thrown from this function will immediately
 *       // exit the CongruenceClosure call.  A subsequent call to
 *       // doPendingMerges() is necessary to continue merging;
 *       // doPendingMerges() is automatically done at the very beginning
 *       // of every call, including find() and areCongruent(), to ensure
 *       // consistency.  However, if the context pops, the pending merges
 *       // up to that level are cleared.
 *     }
 *   };
 */
template <class OutputChannel>
class CongruenceClosure {
  /** The output channel */
  OutputChannel* d_out;

public:
  /** Construct a congruence closure module instance */
  CongruenceClosure(context::Context* ctxt, OutputChannel* out)
    throw(AssertionException);

  /**
   * Add a term into CC consideration.
   */
  void addTerm(TNode trm) throw(AssertionException);

  /**
   * Add an equality literal eq into CC consideration.
   */
  void addEquality(TNode eq) throw(AssertionException);

  /**
   * Inquire whether two expressions are congruent.
   */
  bool areCongruent(TNode a, TNode b) throw(AssertionException);

  /**
   * Find the EC representative for a term t
   */
  TNode find(TNode t) throw(AssertionException);

  /**
   * Request an explanation for why a and b are in the same EC.
   * Throws a CongruenceClosureException if they aren't in the same
   * EC.
   */
  Node explain(TNode a, TNode b)
    throw(CongruenceClosureException, AssertionException);

  /**
   * Request an explanation for why the lhs and rhs of this equality
   * are in the same EC.  Throws a CongruenceClosureException if they
   * aren't in the same EC.
   */
  Node explain(TNode eq)
    throw(CongruenceClosureException, AssertionException);

  /**
   * Request that any pending merges (canceled with an
   * exception thrown from OutputChannel::merge()) be
   * performed and the OutputChannel notified.
   */
  void doPendingMerges() throw(AssertionException);

private:

  /**
   * Internal propagation of information.
   */
  void propagate();

  /**
   * Internal lookup mapping.
   */
  TNode lookup(TNode a);

  /**
   * Internal lookup mapping.
   */
  void setLookup(TNode a, TNode b);

  /**
   * Internal normalization.
   */
  Node normalize(TNode t);
};

}/* CVC4 namespace */

#endif /* __CVC4__UTIL__CONGRUENCE_CLOSURE_H */
