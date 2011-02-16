/*********************                                                        */
/*! \file unate_propagator.cpp
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

#include "theory/arith/unate_propagator.h"
#include "theory/arith/arith_utilities.h"

#include <list>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

using namespace CVC4::kind;

using namespace std;

struct PropagatorLeqSetID {};
typedef expr::Attribute<PropagatorLeqSetID, OrderedSet*, SetCleanupStrategy> PropagatorLeqSet;

struct PropagatorEqSetID {};
typedef expr::Attribute<PropagatorEqSetID, OrderedSet*, SetCleanupStrategy> PropagatorEqSet;

struct PropagatorGeqSetID {};
typedef expr::Attribute<PropagatorGeqSetID, OrderedSet*, SetCleanupStrategy> PropagatorGeqSet;

ArithUnatePropagator::ArithUnatePropagator(context::Context* cxt, OutputChannel& out) :
  d_arithOut(out)
{ }

bool ArithUnatePropagator::leftIsSetup(TNode left){
  return left.hasAttribute(PropagatorEqSet());
}

bool ArithUnatePropagator::hasAnyAtoms(TNode v){
  Assert(!leftIsSetup(v)
         || !v.getAttribute(PropagatorEqSet())->empty()
         || !v.getAttribute(PropagatorLeqSet())->empty()
         || !v.getAttribute(PropagatorGeqSet())->empty());

  return leftIsSetup(v);
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
      addEqualityToEqualities(atom, eqSet, res.first);
      addEqualityToLeqs(atom, leqSet);
      addEqualityToGeqs(atom, geqSet);
      break;
    }
  case LEQ:
    {
      pair<OrderedSet::iterator, bool> res = leqSet->insert(atom);
      Assert(res.second);

      addLeqToLeqs(atom, leqSet, res.first);
      addLeqToEqualities(atom, eqSet);
      addLeqToGeqs(atom, geqSet);
      break;
    }
  case GEQ:
    {
      pair<OrderedSet::iterator, bool> res = geqSet->insert(atom);
      Assert(res.second);

      addGeqToGeqs(atom, geqSet, res.first);
      addGeqToEqualities(atom, eqSet);
      addGeqToLeqs(atom, leqSet);

      break;
    }
  default:
    Unreachable();
  }
}

bool rightHandRationalIsEqual(TNode a, TNode b){
  TNode secondA = a[1];
  TNode secondB = b[1];

  const Rational& qA = secondA.getConst<Rational>();
  const Rational& qB = secondB.getConst<Rational>();

  return qA == qB;
}
bool rightHandRationalIsLT(TNode a, TNode b){
  TNode secondA = a[1];
  TNode secondB = b[1];

  const Rational& qA = secondA.getConst<Rational>();
  const Rational& qB = secondB.getConst<Rational>();

  return qA < qB;
}

void ArithUnatePropagator::addEqualityToEqualities(TNode atom,
                                                   OrderedSet* eqSet,
                                                   OrderedSet::iterator eqPos){
  Assert(atom.getKind() == EQUAL);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);
  for(OrderedSet::iterator eqIter = eqSet->begin();
      eqIter != eqSet->end(); ++eqIter){
    if(eqIter == eqPos) continue;
    TNode eq = *eqIter;
    Assert(!rightHandRationalIsEqual(eq, atom));
    addImplication(eq, negation);
  }
}

void ArithUnatePropagator::addEqualityToLeqs(TNode atom, OrderedSet* leqSet)
{
  Assert(atom.getKind() == EQUAL);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

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
}

void ArithUnatePropagator::addEqualityToGeqs(TNode atom, OrderedSet* geqSet){

  Assert(atom.getKind() == EQUAL);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

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
      if(geqIter != geqSet->begin()){
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
    addImplication(atom, strictlyLT);// x=b /\ b > b' => x >= b'
  }else{
    Assert(geqSet->empty());
  }
}

void ArithUnatePropagator::addLeqToLeqs
(TNode atom,
 OrderedSet* leqSet,
 OrderedSet::iterator atomPos)
{
  Assert(atom.getKind() == LEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  if(atomPos != leqSet->begin()){
    --atomPos;
    TNode beforeLeq = *atomPos;
    Assert(rightHandRationalIsLT(beforeLeq, atom));
    addImplication(beforeLeq, atom);// x<=b' /\ b' < b => x <= b
    ++atomPos;
  }
  ++atomPos;
  if(atomPos != leqSet->end()){
    TNode afterLeq = *atomPos;
    Assert(rightHandRationalIsLT(atom, afterLeq));
    addImplication(atom, afterLeq);// x<=b /\ b < b' => x <= b'
  }
}
void ArithUnatePropagator::addLeqToGeqs(TNode atom, OrderedSet* geqSet) {

  Assert(atom.getKind() == LEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  OrderedSet::iterator geqIter = geqSet->lower_bound(atom);
  if(geqIter != geqSet->end()){
    TNode lowerBound = *geqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      Assert(rightHandRationalIsEqual(atom, lowerBound));
      addImplication(negation, lowerBound);// (x > b) => (x >= b)
      ++geqIter;
      if(geqIter != geqSet->end()){
        TNode next = *geqIter;
        Assert(rightHandRationalIsLT(atom, next));
        addImplication(next, negation);// x>=b' /\ b' > b => x > b
      }
    }else{
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(lowerBound, negation);// x>=b' /\ b' > b => x > b
      if(geqIter != geqSet->begin()){
        --geqIter;
        TNode prev = *geqIter;
        Assert(rightHandRationalIsLT(prev, atom));
        addImplication(negation, prev);// (x>b /\ b > b') => x >= b'
      }
    }
  }else if(geqIter != geqSet->begin()){
    --geqIter;
    TNode strictlyLT = *geqIter;
    Assert(rightHandRationalIsLT(strictlyLT, atom));
    addImplication(negation, strictlyLT);// (x>b /\ b > b') => x >= b'
  }else{
    Assert(geqSet->empty());
  }
}

void ArithUnatePropagator::addLeqToEqualities(TNode atom, OrderedSet* eqSet) {
  Assert(atom.getKind() == LEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  //TODO Improve this later
  for(OrderedSet::iterator eqIter = eqSet->begin(); eqIter != eqSet->end(); ++eqIter){
    TNode eq = *eqIter;
    if(rightHandRationalIsEqual(atom, eq)){
      // (x = b' /\ b = b') =>  x <= b
      addImplication(eq, atom);
    }else if(rightHandRationalIsLT(atom, eq)){
      // (x = b' /\ b' > b) =>  x > b
      addImplication(eq, negation);
    }else{
      // (x = b' /\ b' < b) =>  x <= b
      addImplication(eq, atom);
    }
  }
}


void ArithUnatePropagator::addGeqToGeqs
(TNode atom, OrderedSet* geqSet, OrderedSet::iterator atomPos)
{
  Assert(atom.getKind() == GEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  if(atomPos != geqSet->begin()){
    --atomPos;
    TNode beforeGeq = *atomPos;
    Assert(rightHandRationalIsLT(beforeGeq, atom));
    addImplication(atom, beforeGeq);// x>=b /\ b > b' => x >= b'
    ++atomPos;
  }
  ++atomPos;
  if(atomPos != geqSet->end()){
    TNode afterGeq = *atomPos;
    Assert(rightHandRationalIsLT(atom, afterGeq));
    addImplication(afterGeq, atom);// x>=b' /\ b' > b => x >= b
  }
}

void ArithUnatePropagator::addGeqToLeqs(TNode atom, OrderedSet* leqSet){

  Assert(atom.getKind() == GEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  OrderedSet::iterator leqIter = leqSet->lower_bound(atom);
  if(leqIter != leqSet->end()){
    TNode lowerBound = *leqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      Assert(rightHandRationalIsEqual(atom, lowerBound));
      addImplication(negation, lowerBound);// (x < b) => (x <= b)

      if(leqIter != leqSet->begin()){
        --leqIter;
        TNode prev = *leqIter;
        Assert(rightHandRationalIsLT(prev, atom));
        addImplication(prev, negation);// x<=b' /\ b' < b => x < b
      }
    }else{
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(negation, lowerBound);// (x < b /\ b < b') => x <= b'
      ++leqIter;
      if(leqIter != leqSet->end()){
        TNode next = *leqIter;
        Assert(rightHandRationalIsLT(atom, next));
        addImplication(negation, next);// (x < b /\ b < b') => x <= b'
      }
    }
  }else if(leqIter != leqSet->begin()){
    --leqIter;
    TNode strictlyLT = *leqIter;
    Assert(rightHandRationalIsLT(strictlyLT, atom));
    addImplication(strictlyLT, negation);// (x <= b' /\ b' < b) => x < b
  }else{
    Assert(leqSet->empty());
  }
}
void ArithUnatePropagator::addGeqToEqualities(TNode atom, OrderedSet* eqSet){

  Assert(atom.getKind() == GEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  //TODO Improve this later
  for(OrderedSet::iterator eqIter = eqSet->begin(); eqIter != eqSet->end(); ++eqIter){
    TNode eq = *eqIter;
    if(rightHandRationalIsEqual(atom, eq)){
      // (x = b' /\ b = b') =>  x >= b
      addImplication(eq, atom);
    }else if(rightHandRationalIsLT(eq, atom)){
      // (x = b' /\ b' < b) =>  x < b
      addImplication(eq, negation);
    }else{
      // (x = b' /\ b' > b) =>  x >= b
      addImplication(eq, atom);
    }
  }
}

void ArithUnatePropagator::addImplication(TNode a, TNode b){
  Node imp = NodeBuilder<2>(IMPLIES) << a << b;

  Debug("arith-propagate") << "ArithUnatePropagator::addImplication";
  Debug("arith-propagate") << "(" << a << ", " << b <<")" << endl;

  d_arithOut.lemma(imp);
}
