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
 ** [[ Add file-specific comments here ]]
 **/


#ifndef __CVC4__THEORY__THEORY_UF_H
#define __CVC4__THEORY__THEORY_UF_H

#include "expr/node.h"
#include "expr/attribute.h"

#include "theory/theory.h"
#include "theory/output_channel.h"

#include "context/context.h"
#include "theory/uf/ecdata.h"

namespace CVC4 {
namespace theory {


class TheoryUF : public Theory {
private:

  /**
   * The associated context. Needed for allocating context dependent objects
   * and objects in context dependent memory.
   */
  context::Context* d_context;
  
  /** List of pending equivalence class merges. */
  context::CDList<Node> d_pending;

  /** Index of the next pending equality to merge. */
  context::CDO<unsigned> d_currentPendingIdx;

  /** List of all disequalities this theory has seen. */
  context::CDList<Node> d_disequality;


public:

  TheoryUF(context::Context* c);
  ~TheoryUF();

  void registerTerm(TNode n);
  
  
  void check(OutputChannel& out, Effort level= FULL_EFFORT);

  void propagate(OutputChannel& out, Effort level= FULL_EFFORT){}

  void explain(OutputChannel& out,
               const Node& n,
               Effort level = FULL_EFFORT){}

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
  bool equiv(Node x, Node y);

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

  /* Performs Congruence Closure to reflect the new additions to d_pending. */
  void merge();

};



struct ECCleanupFcn{
  static void cleanup(ECData* & ec){
    ec->deleteSelf();
  }
};

struct EquivClass;
typedef expr::Attribute<EquivClass, ECData* /*, ECCleanupFcn*/> ECAttr;

} /* CVC4::theory namespace */
} /* CVC4 namespace */


#endif /* __CVC4__THEORY__THEORY_UF_H */
