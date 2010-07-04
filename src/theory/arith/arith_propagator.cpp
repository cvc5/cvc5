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

void ArithUnatePropagator::addEquality
(TNode atom,
 OrderedSet* eqSet,
 OrderedSet* leqSet,
 OrderedSet* geqSet,
 OrderedSet::iterator eqPos)
{
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);
  for(OrderedSet::iterator eqIter = eqSet->begin();
      eqIter != eqSet->end(); ++eqIter){
    if(eqIter == eqPos) continue;
    TNode eq = *eqIter;
    Assert(!rightHandRationalIsEqual(eq, atom));
    addImplication(eq, negation, "125");
  }

  OrderedSet::iterator leqIter = leqSet->lower_bound(atom);
  if(leqIter != leqSet->end()){
    TNode lowerBound = *leqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      addImplication(atom, lowerBound, "132");  // x=b /\ b = b' => x <= b'
      if(leqIter != leqSet->begin()){
        --leqIter;
        Assert(rightHandRationalIsLT(*leqIter, atom));
        addImplication(*leqIter, negation, "136"); // x=b /\ b > b' => x > b'
      }
    }else{
      //probably wrong
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(atom, lowerBound, "141");// x=b /\ b < b' => x <= b'

      if(leqIter != leqSet->begin()){
        --leqIter;
        Assert(rightHandRationalIsLT(*leqIter, atom));
        addImplication(*leqIter, negation, "146");// x=b /\ b > b' => x > b'
      }
    }
  }else if(leqIter != leqSet->begin()){
    --leqIter;
    TNode strictlyLessThan = *leqIter;
    Assert(rightHandRationalIsLT(strictlyLessThan, atom));
    addImplication(*leqIter, negation, "153"); // x=b /\ b < b' => x <= b'
  }else{
    Assert(leqSet->empty());
  }

  OrderedSet::iterator geqIter = geqSet->lower_bound(atom);
  if(geqIter != geqSet->end()){
    TNode lowerBound = *geqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      addImplication(atom, lowerBound, "162");  // x=b /\ b = b' => x >= b'
      ++geqIter;
      if(geqIter != geqSet->end()){ // x=b /\ b < b' => x < b'
        TNode strictlyGt = *geqIter;
        Assert(rightHandRationalIsLT( atom, strictlyGt ));
        addImplication(strictlyGt, negation, "167");
      }
    }else{
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(lowerBound, negation, "171");// x=b /\ b < b' => x < b'
      if(geqIter != geqSet->end()){
        --geqIter;
        TNode strictlyLessThan = *geqIter;
        Assert(rightHandRationalIsLT(strictlyLessThan, atom));
        addImplication(atom, strictlyLessThan, "176");// x=b /\ b > b' => x >= b'
      }
    }
  }else if(geqIter != geqSet->begin()){
    --geqIter;
    TNode strictlyLT = *geqIter;
    Assert(rightHandRationalIsLT(strictlyLT, atom));
    addImplication(atom, strictlyLT, "183");// x=b /\ b > b' => x >= b'
  }else{
    Assert(geqSet->empty());
  }
}

void ArithUnatePropagator::addLeq
(TNode atom,
 OrderedSet* eqSet,
 OrderedSet* leqSet,
 OrderedSet* geqSet,
 OrderedSet::iterator atomPos)
{
  Assert(atom.getKind() == LEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  if(atomPos != leqSet->begin()){
    --atomPos;
    TNode beforeLeq = *atomPos;
    Assert(rightHandRationalIsLT(beforeLeq, atom));
    addImplication(beforeLeq, atom, "203");// x<=b' /\ b' < b => x <= b
    ++atomPos;
  }
  ++atomPos;
  if(atomPos != leqSet->end()){
    TNode afterLeq = *atomPos;
    Assert(rightHandRationalIsLT(atom, afterLeq));
    addImplication(atom, afterLeq, "210");// x<=b /\ b < b' => x <= b'
  }


  OrderedSet::iterator geqIter = geqSet->lower_bound(atom);
  if(geqIter != geqSet->end()){
    TNode lowerBound = *geqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      Assert(rightHandRationalIsEqual(atom, lowerBound));
      addImplication(negation, lowerBound, "219");// (x > b) => (x >= b)
      ++geqIter;
      if(geqIter != geqSet->end()){
        TNode next = *geqIter;
        Assert(rightHandRationalIsLT(atom, next));
        addImplication(next, negation, "224");// x>=b' /\ b' > b => x > b
      }
    }else{
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(lowerBound, negation, "228");// x>=b' /\ b' > b => x > b
      if(geqIter != geqSet->begin()){
        --geqIter;
        TNode prev = *geqIter;
        Assert(rightHandRationalIsLT(prev, atom));
        addImplication(negation, prev, "233");// (x>b /\ b > b') => x >= b'
      }
    }
  }else if(geqIter != geqSet->begin()){
    --geqIter;
    TNode strictlyLT = *geqIter;
    Assert(rightHandRationalIsLT(strictlyLT, atom));
    addImplication(negation, strictlyLT, "240");// (x>b /\ b > b') => x >= b'
  }else{
    Assert(geqSet->empty());
  }

  //TODO Improve this later
  for(OrderedSet::iterator eqIter = eqSet->begin(); eqIter != eqSet->end(); ++eqIter){
    TNode eq = *eqIter;
    if(rightHandRationalIsEqual(atom, eq)){
      // (x = b' /\ b = b') =>  x <= b
      addImplication(eq, atom, "250");
    }else if(rightHandRationalIsLT(atom, eq)){
      // (x = b' /\ b' > b) =>  x > b
      addImplication(eq, negation, "253");
    }else{
      // (x = b' /\ b' < b) =>  x <= b
      addImplication(eq, atom, "256");
    }
  }
}

void ArithUnatePropagator::addGeq
(TNode atom,
 OrderedSet* eqSet,
 OrderedSet* leqSet,
 OrderedSet* geqSet,
 OrderedSet::iterator atomPos)
{
  Assert(atom.getKind() == GEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  if(atomPos != geqSet->begin()){
    --atomPos;
    TNode beforeGeq = *atomPos;
    Assert(rightHandRationalIsLT(beforeGeq, atom));
    addImplication(atom, beforeGeq, "275");// x>=b /\ b > b' => x >= b'
    ++atomPos;
  }
  ++atomPos;
  if(atomPos != geqSet->end()){
    TNode afterGeq = *atomPos;
    Assert(rightHandRationalIsLT(atom, afterGeq));
    addImplication(afterGeq, atom, "282");// x>=b' /\ b' > b => x >= b
  }

  OrderedSet::iterator leqIter = leqSet->lower_bound(atom);
  if(leqIter != leqSet->end()){
    TNode lowerBound = *leqIter;
    if(rightHandRationalIsEqual(atom, lowerBound)){
      Assert(rightHandRationalIsEqual(atom, lowerBound));
      addImplication(negation, lowerBound, "290");// (x < b) => (x <= b)

      if(leqIter != leqSet->begin()){
        --leqIter;
        TNode prev = *leqIter;
        Assert(rightHandRationalIsLT(prev, atom));
        addImplication(prev, negation, "296");// x<=b' /\ b' < b => x < b
      }
    }else{
      Assert(rightHandRationalIsLT(atom, lowerBound));
      addImplication(negation, lowerBound, "300");// (x < b /\ b < b') => x <= b'
      ++leqIter;
      if(leqIter != leqSet->end()){
        TNode next = *leqIter;
        Assert(rightHandRationalIsLT(atom, next));
        addImplication(negation, next, "305");// (x < b /\ b < b') => x <= b'
      }
    }
  }else if(leqIter != leqSet->begin()){
    --leqIter;
    TNode strictlyLT = *leqIter;
    Assert(rightHandRationalIsEqual(strictlyLT, atom));
    addImplication(strictlyLT, negation, "312");// (x <= b' /\ b' < b) => x < b
  }else{
    Assert(leqSet->empty());
  }

  //TODO Improve this later
  for(OrderedSet::iterator eqIter = eqSet->begin(); eqIter != eqSet->end(); ++eqIter){
    TNode eq = *eqIter;
    if(rightHandRationalIsEqual(atom, eq)){
      // (x = b' /\ b = b') =>  x >= b
      addImplication(eq, atom, "322");
    }else if(rightHandRationalIsLT(eq, atom)){
      // (x = b' /\ b' < b) =>  x < b
      addImplication(eq, negation, "325");
    }else{
      // (x = b' /\ b' > b) =>  x >= b
      addImplication(eq, atom, "328");
    }
  }
}



Node miniReduce(TNode a){
  switch(a.getKind()){
  case GEQ:
  case EQUAL:
  case LEQ:
    return a;
  case NOT:
    if(a[0].getKind() == NOT){
      return miniReduce((a[0])[0]);
    }else{
      return NodeManager::currentNM()->mkNode(NOT, miniReduce(a[0]));
    }
  case IMPLIES:
    {
      Node negateFirst = NodeManager::currentNM()->mkNode(NOT, a[0]);
      Node reduceNegateFirst = miniReduce(negateFirst);
      Node reduceSecond = miniReduce(a[1]);
      return NodeManager::currentNM()->mkNode(OR, reduceNegateFirst, reduceSecond);
    }
  default:
    Unreachable();
    return Node::null();
  }
}

void ArithUnatePropagator::addImplication(TNode a, TNode b, const char* c){
  Node imp = NodeManager::currentNM()->mkNode(IMPLIES, a, b);

  static set<const char*> set;


  Debug("arith-propagate") << "Adding propagation lemma " << c << endl
                           << "\t" << a << endl
                           << "\t" << b << endl;

  if(set.find(c) == set.end()){
    set.insert(c);
    Debug("arith-propagate") << "print set size " << set.size() << endl;
  }
  Node reduce = miniReduce(imp);

  d_arith->addInternalLemma(imp);
}
