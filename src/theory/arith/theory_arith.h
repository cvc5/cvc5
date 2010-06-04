/*********************                                                        */
/*! \file theory_arith.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Arithmetic theory.
 **
 ** Arithmetic theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__THEORY_ARITH_H
#define __CVC4__THEORY__ARITH__THEORY_ARITH_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdlist.h"
#include "expr/node.h"

#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/partial_model.h"

#include <vector>
#include <queue>

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArith : public Theory {
private:
  /* Chopping block begins */

  std::vector<Node> d_splits;
  //This stores the eager splits sent out of the theory.
  //TODO get rid of this.

  context::CDList<Node> d_preprocessed;
  //TODO This is currently needed to save preprocessed nodes that may not
  //currently have an outisde reference. Get rid of when preprocessing is occuring
  //correctly.

  std::vector<Node> d_variables;
  //TODO get rid of this.  Currently forces every variable and skolem constant that
  // can hit the tableau to stay alive forever!
  //This needs to come before d_partialModel and d_tableau in the file


  std::priority_queue<Node> d_possiblyInconsistent;

  /* Chopping block ends */
  ArithConstants d_constants;
  ArithPartialModel d_partialModel;

  context::CDList<Node> d_diseq;
  Tableau d_tableau;
  ArithRewriter d_rewriter;



public:
  TheoryArith(context::Context* c, OutputChannel& out);
  ~TheoryArith();

  Node rewrite(TNode n);

  void preRegisterTerm(TNode n);
  void registerTerm(TNode n);
  void check(Effort e);
  void propagate(Effort e) { Unimplemented(); }
  void explain(TNode n, Effort e) { Unimplemented(); }

private:
  bool AssertLower(TNode n, TNode orig);
  bool AssertUpper(TNode n, TNode orig);
  void update(TNode x_i, DeltaRational& v);
  void pivotAndUpdate(TNode x_i, TNode x_j, DeltaRational& v);

  Node updateInconsistentVars();

  TNode selectSlackBelow(TNode x_i);
  TNode selectSlackAbove(TNode x_i);
  TNode selectSmallestInconsistentVar();

  Node generateConflictAbove(TNode conflictVar);
  Node generateConflictBelow(TNode conflictVar);

  void setupVariable(TNode x);
  DeltaRational computeRowValueUsingAssignment(TNode x);
  DeltaRational computeRowValueUsingSavedAssignment(TNode x);
  void checkTableau();

  void checkBasicVariable(TNode basic);

  //TODO get rid of this!
  Node simulatePreprocessing(TNode n);

};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */
