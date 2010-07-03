/*********************                                                        */
/*! \file arith_propagator.cpp
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

#include "theory/arith/arith_propagator.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/theory_arith.h"

#include <list>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

using namespace CVC4::kind;

using namespace std;

ArithUnatePropagator::ArithUnatePropagator(context::Context* cxt, TheoryArith* arith) :
  d_arith(arith)
{ }

bool ArithUnatePropagator::leftIsSetup(TNode left){
  return left.hasAttribute(PropagatorEqSet());
}

void ArithUnatePropagator::setupLefthand(TNode left){
  Assert(!leftIsSetup(left));

  OrderedSet* eqList = new OrderedSet();
  OrderedSet* leqList = new OrderedSet();
  OrderedSet* geqList = new OrderedSet();

  left.setAttribute(PropagatorEqSet(), eqList);
  left.setAttribute(PropagatorLeqSet(), geqList);
  left.setAttribute(PropagatorGeqSet(), leqList);
}

void ArithUnatePropagator::addAtom(TNode atom){
  TNode left  = atom[0];
  TNode right = atom[1];

  if(!leftIsSetup(left)){
    setupLefthand(left);
  }

  OrderedSet* eqSet = left.getAttribute(PropagatorEqSet());
  OrderedSet* leqSet = left.getAttribute(PropagatorLeqSet());
  OrderedSet* geqSet = left.getAttribute(PropagatorGeqSet());

  switch(atom.getKind()){
  case EQUAL:
    {
      pair<OrderedSet::iterator, bool> res = eqSet->insert(atom);
      Assert(res.second);
      addEquality(atom, eqSet, leqSet, geqSet, res.first);
      break;
    }
  case LEQ:
    {
      pair<OrderedSet::iterator, bool> res = leqSet->insert(atom);
      Assert(res.second);
      addLeq(atom, eqSet, leqSet, geqSet, res.first);
      break;
    }
  case GEQ:
    {
      pair<OrderedSet::iterator, bool> res = geqSet->insert(atom);
      Assert(res.second);
      addGeq(atom, eqSet, leqSet, geqSet, res.first);
      break;
    }
  default:
    Unreachable();
  }
}

void ArithUnatePropagator::addEquality(TNode atom, OrderedSet* eqList, OrderedSet* leqList, OrderedSet* geqList, OrderedSet::iterator eqPos){
  Unimplemented();
}

void ArithUnatePropagator::addLeq(TNode atom, OrderedSet* eqList, OrderedSet* leqList, OrderedSet* geqList, OrderedSet::iterator atomPos){
  Unimplemented();
}

void ArithUnatePropagator::addGeq(TNode atom, OrderedSet* eqList, OrderedSet* leqList, OrderedSet* geqList, OrderedSet::iterator atomPos){
  Unimplemented();
}



void ArithUnatePropagator::addImplication(TNode a, TNode b){
  Node imp = NodeManager::currentNM()->mkNode(IMPLIES, a, b);

  Debug("arith-propagate") << "Adding propagation lemma " << imp << endl;

  d_arith->addInternalLemma(imp);
}
