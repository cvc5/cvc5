/*********************                                                        */
/** theory_uf.h
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
 **
 **/


#ifndef __CVC4__THEORY__THEORY_UF_H
#define __CVC4__THEORY__THEORY_UF_H

#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/theory.h"

#include "context/context.h"
#include "theory/uf/ecdata.h"

namespace CVC4 {
namespace theory {
namespace uf {

class TheoryUF : public TheoryImpl<TheoryUF> {

private:



  /**
   * The associated context. Needed for allocating context dependent objects
   * and objects in context dependent memory.
   */
  context::Context* d_context;

  /** 
   * List of pending equivalence class merges. 
   *
   * Tricky part:
   * Must keep a hard link because new equality terms are created and appended
   * to this list.
   */
  context::CDList<Node> d_pending;

  /** Index of the next pending equality to merge. */
  context::CDO<unsigned> d_currentPendingIdx;

  /** List of all disequalities this theory has seen. */
  context::CDList<Node> d_disequality;

  /**
   * List of all of the terms that are registered in the current context.
   * When registerTerm is called on a term we want to guarentee that there
   * is a hard link to the term for the duration of the context in which
   * register term is called.
   * This invariant is enough for us to use soft links where we want is the
   * current implementation as well as making ECAttr() not context dependent.
   * Soft links used both in ECData, and Link.
   */
  context::CDList<Node> d_registered;

public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUF(context::Context* c, OutputChannel& out);

  /** Destructor for the TheoryUF object. */
  ~TheoryUF();


  //TODO Tim: I am going to delay documenting these functions while Morgan
  //has pending changes to the contracts

  void registerTerm(TNode n);
  void preRegisterTerm(TNode n);

  void check(Effort level);

  void propagate(Effort level) {}

  void explain(TNode n, Effort level) {}

private:
  /**
   * Checks whether 2 nodes are already in the same equivalence class tree.
   * This should only be used internally, and it should only be done when
   * the only thing done with the equivalence classes is an equality check.
   *
   * @returns true iff ccFind(x) == ccFind(y);
   */
  bool sameCongruenceClass(TNode x, TNode y);

  /**
   * Checks whether Node x and Node y are currently congruent
   * using the equivalence class data structures.
   * @returns true iff
   *    |x| = n = |y| and
   *    x.getOperator() == y.getOperator() and
   *    forall 1 <= i < n : ccFind(x[i]) == ccFind(y[i])
   */
  bool equiv(TNode x, TNode y);

  /**
   * Merges 2 equivalence classes, checks wether any predecessors need to
   * be set equal to complete congruence closure.
   * The class with the smaller class size will be merged.
   * @pre ecX->isClassRep()
   * @pre ecY->isClassRep()
   */
  void ccUnion(ECData* ecX, ECData* ecY);

  /**
   * Returns the representative of the equivalence class.
   * May modify the find pointers associated with equivalence classes.
   */
  ECData* ccFind(ECData* x);

  /** Performs Congruence Closure to reflect the new additions to d_pending. */
  void merge();

  /** Constructs a conflict from an inconsistent disequality. */
  Node constructConflict(TNode diseq);

};


/**
 * Cleanup function for ECData. This will be used for called whenever
 * a ECAttr is being destructed.
 */
struct ECCleanupFcn{
  static void cleanup(ECData* & ec){
    ec->deleteSelf();
  }
};

/** Unique name to use for constructing ECAttr. */
struct EquivClass;

/**
 * ECAttr is the attribute that maps a node to an equivalence class.
 */
typedef expr::Attribute<EquivClass, ECData* /*, ECCleanupFcn*/> ECAttr;

} /* CVC4::theory::uf namespace */
} /* CVC4::theory namespace */
} /* CVC4 namespace */


#endif /* __CVC4__THEORY__THEORY_UF_H */
