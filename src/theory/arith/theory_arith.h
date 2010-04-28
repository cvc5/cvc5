/*********************                                                        */
/** theory_arith.h
 ** Original author: mdeters
 ** Major contributors: taking
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.
 **
 ** Arithmetic theory.
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__THEORY_ARITH_H
#define __CVC4__THEORY__ARITH__THEORY_ARITH_H

#include "theory/theory.h"
#include "context/context.h"
#include "context/cdlist.h"

#include "theory/arith/delta_rational.h"
#include "theory/arith/tableau.h"
#include "theory/arith/arith_rewriter.h"

namespace CVC4 {
namespace theory {
namespace arith {

class TheoryArith : public Theory {
private:
  ArithConstants d_constants;

  context::CDList<Node> d_diseq;
  Tableau d_tableau;
  ArithRewriter d_rewriter;

public:
  TheoryArith(context::Context* c, OutputChannel& out) :
    Theory(c, out),
    d_constants(NodeManager::currentNM()), d_diseq(c), d_rewriter(&d_constants)
  {}

  Node rewrite(TNode n);

  void preRegisterTerm(TNode n) { Unimplemented(); }
  void registerTerm(TNode n);
  void check(Effort e);
  void propagate(Effort e) { Unimplemented(); }
  void explain(TNode n, Effort e) { Unimplemented(); }

private:
  void AssertLower(TNode n);
  void AssertUpper(TNode n);
  void update(TNode x_i, DeltaRational& v);
  void pivotAndUpdate(TNode x_i, TNode x_j, DeltaRational& v);
  TNode updateInconsistentVars();

  TNode selectSlackBelow(TNode x_i);
  TNode selectSlackAbove(TNode x_i);
  TNode selectSmallestInconsistentVar();

  Node generateConflictAbove(TNode conflictVar);
  Node generateConflictBelow(TNode conflictVar);

};

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */
