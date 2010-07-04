/*********************                                                        */
/*! \file arith_propagator.h
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/



#include "cvc4_private.h"

#ifndef __CVC4__THEORY__ARITH__ARITH_PROPAGATOR_H
#define __CVC4__THEORY__ARITH__ARITH_PROPAGATOR_H

#include "expr/node.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "context/cdo.h"

#include "theory/arith/ordered_set.h"



namespace CVC4 {
namespace theory {
namespace arith {

struct RightHandRationalLT;
class TheoryArith;

class ArithUnatePropagator {
private:
  TheoryArith* d_arith;

public:
  ArithUnatePropagator(context::Context* cxt, TheoryArith* arith);

  void addAtom(TNode atom);

private:
  void addImplication(TNode a, TNode b, const char *);
  bool leftIsSetup(TNode left);
  void setupLefthand(TNode left);
  void addEquality(TNode atom, OrderedSet* eqSet, OrderedSet* leqSet, OrderedSet* geqSet, OrderedSet::iterator atomPos);
  void addLeq(TNode atom, OrderedSet* eqSet,OrderedSet* leqSet, OrderedSet* geqSet, OrderedSet::iterator atomPos);
  void addGeq(TNode atom, OrderedSet* eqSet, OrderedSet* leqSet, OrderedSet* geqSet, OrderedSet::iterator atomPos);

};


struct PropagatorLeqSetID {};
typedef expr::Attribute<PropagatorLeqSetID, OrderedSet*, SetCleanupStrategy> PropagatorLeqSet;

struct PropagatorEqSetID {};
typedef expr::Attribute<PropagatorEqSetID, OrderedSet*, SetCleanupStrategy> PropagatorEqSet;

struct PropagatorGeqSetID {};
typedef expr::Attribute<PropagatorGeqSetID, OrderedSet*, SetCleanupStrategy> PropagatorGeqSet;

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__ARITH__THEORY_ARITH_H */
