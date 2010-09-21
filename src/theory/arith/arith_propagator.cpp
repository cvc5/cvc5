/*********************                                                        */
/*! \file arith_propagator.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
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

#include <list>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;
using namespace CVC4::theory::arith::propagator;

using namespace CVC4::kind;

using namespace std;

ArithUnatePropagator::ArithUnatePropagator(context::Context* cxt) :
  d_assertions(cxt), d_pendingAssertions(cxt,0)
{ }


bool acceptedKinds(Kind k){
  switch(k){
  case EQUAL:
  case LEQ:
  case GEQ:
    return true;
  default:
    return false;
  }
}

void ArithUnatePropagator::addAtom(TNode atom){
  Assert(acceptedKinds(atom.getKind()));

  TNode left  = atom[0];
  TNode right = atom[1];

  if(!leftIsSetup(left)){
    setupLefthand(left);
  }

  switch(atom.getKind()){
  case EQUAL:
    {
      OrderedBoundsList* eqList = left.getAttribute(propagator::PropagatorEqList());
      Assert(!eqList->contains(atom));
      eqList->append(atom);
      break;
    }
  case LEQ:
    {
      OrderedBoundsList* leqList = left.getAttribute(propagator::PropagatorLeqList());
      Assert(! leqList->contains(atom));
      leqList->append(atom);
      break;
    }
    break;
  case GEQ:
    {
      OrderedBoundsList* geqList = left.getAttribute(propagator::PropagatorGeqList());
      Assert(! geqList->contains(atom));
      geqList->append(atom);
      break;
    }
  default:
    Unreachable();
  }
}
bool ArithUnatePropagator::leftIsSetup(TNode left){
  return left.hasAttribute(propagator::PropagatorEqList());
}

void ArithUnatePropagator::setupLefthand(TNode left){
  Assert(!leftIsSetup(left));

  OrderedBoundsList* eqList = new OrderedBoundsList();
  OrderedBoundsList* geqList = new OrderedBoundsList();
  OrderedBoundsList* leqList = new OrderedBoundsList();

  left.setAttribute(propagator::PropagatorEqList(), eqList);
  left.setAttribute(propagator::PropagatorLeqList(), leqList);
  left.setAttribute(propagator::PropagatorGeqList(), geqList);
}

void ArithUnatePropagator::assertLiteral(TNode lit){

  if(lit.getKind() == NOT){
    Assert(!lit[0].getAttribute(propagator::PropagatorMarked()));
    lit[0].setAttribute(propagator::PropagatorMarked(), true);
  }else{
    Assert(!lit.getAttribute(propagator::PropagatorMarked()));
    lit.setAttribute(propagator::PropagatorMarked(), true);
  }
  d_assertions.push_back(lit);
}

std::vector<Node> ArithUnatePropagator::getImpliedLiterals(){
  std::vector<Node> impliedButNotAsserted;

  while(d_pendingAssertions < d_assertions.size()){
    TNode assertion = d_assertions[d_pendingAssertions];
    d_pendingAssertions = d_pendingAssertions + 1;

    enqueueImpliedLiterals(assertion, impliedButNotAsserted);
  }

  if(Debug.isOn("arith::propagator")){
    for(std::vector<Node>::iterator i = impliedButNotAsserted.begin(),
          endIter = impliedButNotAsserted.end(); i != endIter; ++i){
      Node imp = *i;
      Debug("arith::propagator") << explain(imp) << " (prop)-> " << imp << endl;
    }
  }

  return impliedButNotAsserted;
}

/** This function is effectively a case split. */
void ArithUnatePropagator::enqueueImpliedLiterals(TNode lit, std::vector<Node>& buffer){
  switch(lit.getKind()){
  case EQUAL:
    enqueueEqualityImplications(lit, buffer);
    break;
  case LEQ:
    enqueueUpperBoundImplications(lit, lit, buffer);
    break;
  case GEQ:
    enqueueLowerBoundImplications(lit, lit, buffer);
    break;
  case NOT:
    {
      TNode under = lit[0];
      switch(under.getKind()){
      case EQUAL:
        //Do nothing
        break;;
      case LEQ:
        enqueueLowerBoundImplications(under, lit, buffer);
        break;
      case GEQ:
        enqueueUpperBoundImplications(under, lit, buffer);
        break;
      default:
        Unreachable();
      }
      break;
    }
  default:
    Unreachable();
  }
}

/**
 * An equality (x = c) has been asserted.
 * In this case we can propagate everything by comparing against the other constants.
 */
void ArithUnatePropagator::enqueueEqualityImplications(TNode orig, std::vector<Node>& buffer){
  TNode left = orig[0];
  TNode right = orig[1];
  const Rational& c = right.getConst<Rational>();

  OrderedBoundsList* eqList = left.getAttribute(propagator::PropagatorEqList());
  OrderedBoundsList* leqList = left.getAttribute(propagator::PropagatorLeqList());
  OrderedBoundsList* geqList = left.getAttribute(propagator::PropagatorGeqList());


  /* (x = c) /\ (c !=d) => (x != d)  */
  for(OrderedBoundsList::iterator i = eqList->begin(); i != eqList->end(); ++i){
    TNode eq = *i;
    Assert(eq.getKind() == EQUAL);
    if(!eq.getAttribute(propagator::PropagatorMarked())){ //Note that (x = c) is marked
      Assert(eq[1].getConst<Rational>() != c);

      eq.setAttribute(propagator::PropagatorMarked(), true);

      Node neq = NodeManager::currentNM()->mkNode(NOT, eq);
      neq.setAttribute(propagator::PropagatorExplanation(), orig);
      buffer.push_back(neq);
    }
  }
  for(OrderedBoundsList::iterator i = leqList->begin(); i != leqList->end(); ++i){
    TNode leq = *i;
    Assert(leq.getKind() == LEQ);
    if(!leq.getAttribute(propagator::PropagatorMarked())){
      leq.setAttribute(propagator::PropagatorMarked(), true);
      const Rational& d = leq[1].getConst<Rational>();
      if(c <= d){
        /* (x = c) /\ (c <= d) => (x <= d)  */
        leq.setAttribute(propagator::PropagatorExplanation(), orig);
        buffer.push_back(leq);
      }else{
        /* (x = c) /\ (c > d) => (x > d)  */
        Node gt = NodeManager::currentNM()->mkNode(NOT, leq);
        gt.setAttribute(propagator::PropagatorExplanation(), orig);
        buffer.push_back(gt);
      }
    }
  }

  for(OrderedBoundsList::iterator i = geqList->begin(); i != geqList->end(); ++i){
    TNode geq = *i;
    Assert(geq.getKind() == GEQ);
    if(!geq.getAttribute(propagator::PropagatorMarked())){
      geq.setAttribute(propagator::PropagatorMarked(), true);
      const Rational& d = geq[1].getConst<Rational>();
      if(c >= d){
        /* (x = c) /\ (c >= d) => (x >= d)  */
        geq.setAttribute(propagator::PropagatorExplanation(), orig);
        buffer.push_back(geq);
      }else{
        /* (x = c) /\ (c >= d) => (x >= d)  */
        Node lt = NodeManager::currentNM()->mkNode(NOT, geq);
        lt.setAttribute(propagator::PropagatorExplanation(), orig);
        buffer.push_back(lt);
      }
    }
  }
}

void ArithUnatePropagator::enqueueUpperBoundImplications(TNode atom, TNode orig, std::vector<Node>& buffer){

  Assert(atom.getKind() == LEQ || (orig.getKind() == NOT && atom.getKind() == GEQ));

  TNode left = atom[0];
  TNode right = atom[1];
  const Rational& c = right.getConst<Rational>();

  OrderedBoundsList* eqList = left.getAttribute(propagator::PropagatorEqList());
  OrderedBoundsList* leqList = left.getAttribute(propagator::PropagatorLeqList());
  OrderedBoundsList* geqList = left.getAttribute(propagator::PropagatorGeqList());


  //For every node (x <= d), we will restrict ourselves to look at the cases when (d >= c)
  for(OrderedBoundsList::iterator i = leqList->lower_bound(atom); i != leqList->end(); ++i){
    TNode leq = *i;
    Assert(leq.getKind() == LEQ);
    if(!leq.getAttribute(propagator::PropagatorMarked())){
      leq.setAttribute(propagator::PropagatorMarked(), true);
      const Rational& d = leq[1].getConst<Rational>();
      Assert( c <= d );

      leq.setAttribute(propagator::PropagatorExplanation(), orig);
      buffer.push_back(leq); // (x<=c) /\ (c <= d) => (x <= d)
      //Note that if c=d, that at the node is not marked this can only be reached when (x < c)
      //So we do not have to worry about a circular dependency
    }else if(leq != atom){
      break; //No need to examine the rest, this atom implies the rest of the possible propagataions
    }
  }

  for(OrderedBoundsList::iterator i = geqList->upper_bound(atom); i != geqList->end(); ++i){
    TNode geq = *i;
    Assert(geq.getKind() == GEQ);
    if(!geq.getAttribute(propagator::PropagatorMarked())){
      geq.setAttribute(propagator::PropagatorMarked(), true);
      const Rational& d = geq[1].getConst<Rational>();
      Assert( c < d );

      Node lt = NodeManager::currentNM()->mkNode(NOT, geq);
      lt.setAttribute(propagator::PropagatorExplanation(), orig);
      buffer.push_back(lt); // x<=c /\ d > c => x < d
    }else{
      break; //No need to examine this atom implies the rest
    }
  }

  for(OrderedBoundsList::iterator i = eqList->upper_bound(atom); i != eqList->end(); ++i){
    TNode eq = *i;
    Assert(eq.getKind() == EQUAL);
    if(!eq.getAttribute(propagator::PropagatorMarked())){
      eq.setAttribute(propagator::PropagatorMarked(), true);
      const Rational& d = eq[1].getConst<Rational>();
      Assert( c < d );

      Node neq = NodeManager::currentNM()->mkNode(NOT, eq);
      neq.setAttribute(propagator::PropagatorExplanation(), orig);
      buffer.push_back(neq); // x<=c /\ c < d => x !=  d
    }
  }
}

void ArithUnatePropagator::enqueueLowerBoundImplications(TNode atom, TNode orig, std::vector<Node>& buffer){

  Assert(atom.getKind() == GEQ || (orig.getKind() == NOT && atom.getKind() == LEQ));

  TNode left = atom[0];
  TNode right = atom[1];
  const Rational& c = right.getConst<Rational>();

  OrderedBoundsList* eqList = left.getAttribute(propagator::PropagatorEqList());
  OrderedBoundsList* leqList = left.getAttribute(propagator::PropagatorLeqList());
  OrderedBoundsList* geqList = left.getAttribute(propagator::PropagatorGeqList());


  for(OrderedBoundsList::reverse_iterator i = geqList->reverse_lower_bound(atom);
      i != geqList->rend(); i++){
    TNode geq = *i;
    Assert(geq.getKind() == GEQ);
    if(!geq.getAttribute(propagator::PropagatorMarked())){
      geq.setAttribute(propagator::PropagatorMarked(), true);
      const Rational& d = geq[1].getConst<Rational>();
      Assert( c >= d );

      geq.setAttribute(propagator::PropagatorExplanation(), orig);
      buffer.push_back(geq); // x>=c /\ c >= d => x >= d
    }else if(geq != atom){
      break; //No need to examine the rest, this atom implies the rest of the possible propagataions
    }
  }

  for(OrderedBoundsList::reverse_iterator i = leqList->reverse_upper_bound(atom);
      i != leqList->rend(); ++i){
    TNode leq = *i;
    Assert(leq.getKind() == LEQ);
    if(!leq.getAttribute(propagator::PropagatorMarked())){
      leq.setAttribute(propagator::PropagatorMarked(), true);
      const Rational& d = leq[1].getConst<Rational>();
      Assert( c > d );

      Node gt = NodeManager::currentNM()->mkNode(NOT, leq);
      gt.setAttribute(propagator::PropagatorExplanation(), orig);
      buffer.push_back(gt); // x>=c /\ d < c => x > d
    }else{
      break; //No need to examine this atom implies the rest
    }
  }

  for(OrderedBoundsList::reverse_iterator i = eqList->reverse_upper_bound(atom);
      i != eqList->rend(); ++i){
    TNode eq = *i;
    Assert(eq.getKind() == EQUAL);
    if(!eq.getAttribute(propagator::PropagatorMarked())){
      eq.setAttribute(propagator::PropagatorMarked(), true);
      const Rational& d = eq[1].getConst<Rational>();
      Assert( c > d );

      Node neq = NodeManager::currentNM()->mkNode(NOT, eq);
      neq.setAttribute(propagator::PropagatorExplanation(), orig);
      buffer.push_back(neq); // x>=c /\ c > d => x !=  d
    }
  }

}

Node ArithUnatePropagator::explain(TNode lit){
  Assert(lit.hasAttribute(propagator::PropagatorExplanation()));
  return lit.getAttribute(propagator::PropagatorExplanation());
}
