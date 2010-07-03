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

bool rightHandRationalIsEqual(TNode a, TNode b){
  TNode secondA = a[1];
  TNode secondB = b[1];
  
  const Rational& qA = a.getConst<Rational>();
  const Rational& qB = b.getConst<Rational>();

  return qA == qB;
}
bool rightHandRationalIsLT(TNode a, TNode b){
  TNode secondA = a[1];
  TNode secondB = b[1];
  
  const Rational& qA = a.getConst<Rational>();
  const Rational& qB = b.getConst<Rational>();

  return qA < qB;
}

void ArithUnatePropagator::addEquality
(TNode atom,
 OrderedSet* eqList,
 OrderedSet* leqList,
 OrderedSet* geqList,
 OrderedSet::iterator eqPos){
  TNode negation = NodeManager::currentNM()->mkNode(NOT, atom);
  for(OrderedSet::iterator eqIter = eqSet->begin();
      eqIter != eqSet->end(); ++eqIter){
    if(eqIter == eqPos) continue;
    TNode eq = *eqIter;
    Assert(!rightHandRationalIsEqual(eq, atom));
    addImplication(eq, negation);
  }

  OrderedSet::iterator leqIter = leqSet->lower_bound(atom);
  if(leqIter != leqSet->end()){
    TNode lowerBound = *leqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      addImplication(atom, lowerBound);  // x=b /\ b = b' => x <= b'
      if(leqIter != leqSet->begin()){
	--leqIter;
	Assert(rightHandRationalIsLT(*leqIter, atom));
	addImplication(*leqIter, negation); // x=b /\ b > b' => x > b'
      }
    }else{
      //probably wrong
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(atom, lowerBound);// x=b /\ b < b' => x <= b'

      if(leqIter != leqSet->begin()){
	--leqIter;
	Assert(rightHandRationalIsLT(*leqIter, atom));
	addImplication(*leqIter, negation);// x=b /\ b > b' => x > b'
      }
    }
  }else if(leqIter != leqSet->begin()){
    --leqIter;
    TNode strictlyLessThan = *leqIter;
    Assert(rightHandRationalIsLT(strictlyLessThan, atom));
    addImplication(*leqIter, negation); // x=b /\ b < b' => x <= b'
  }else{
    Assert(leqSet->empty());
  }

  OrderedSet::iterator geqIter = geqSet->lower_bound(atom);
  if(geqIter != geqSet->end()){
    TNode lowerBound = *geqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      addImplication(atom, lowerBound);  // x=b /\ b = b' => x >= b'
      ++geqIter;
      if(geqIter != geqSet->end()){ // x=b /\ b < b' => x < b'
	TNode strictlyGt = *geqIter;
	Assert(rightHandRationalIsLT( atom, strictlyGt ));
	addImplication(strictlyGt, negation);
      }
    }else{
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(lowerBound, negation);// x=b /\ b < b' => x < b'
      if(geqIter != geqSet->end()){
	--geqIter;
	TNode strictlyLessThan = *geqIter;
	Assert(rightHandRationalIsLT(strictlyLessThan, atom));
	addImplication(atom, strictlyLessThan);// x=b /\ b > b' => x >= b'
      }
    }
  }else if(geqIter != geqSet->begin()){
    --geqIter;
    TNode strictlyLT = *geqIter;
    Assert(rightHandRationalIsLT(strictlyLT, atom));
    addImplication(atom, strictlyLessThan);// x=b /\ b > b' => x >= b'
  }else{
    Assert(geqSet->empty());
  }
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
