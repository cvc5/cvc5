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

#include <list>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

using namespace CVC4::kind;

using namespace std;

ArithUnatePropagator::ArithUnatePropagator(context::Context* cxt) :
  d_pendingAssertions(cxt,0),
  d_assertions(cxt)
{ }


inline int orderRelation(Kind k){

  switch(k){
  case EQUAL:
    return 0;
  case LEQ:
    return 1;
  case GEQ:
    return 2;
  default:
    Unreachable();
  }
}

void reduceSymmetries(TNode& atom, Rational& b, TNode& otherAtom, Rational& otherB){
  int orderedA = orderRelation(atom.getKind());
  int orderedOA = orderRelation(otherAtom.getKind());

  if((orderedOA < orderedA) || (orderedOA == orderedA && otherB < b)){
    TNode tmp = atom;
    atom = otherAtom;
    otherAtom = tmp;

    Rational q(b);
    b = otherB;
    otherB = q;
  }
}

void ArithUnatePropagator::addImplication(TNode a0, TNode a1){
  vector<Node>* a0imps = a0.getAttribute(propagator::PropagatorIG());
  a0imps->push_back(a1);
}

void ArithUnatePropagator::introduceImplications(TNode atom, TNode otherAtom){

  Rational b = atom[1].getConst<Rational>();
  Rational otherB = otherAtom[1].getConst<Rational>();

  reduceSymmetries(atom, b, otherAtom, otherB);

  Kind k = atom.getKind();
  Kind otherK = otherAtom.getKind();

  Node negation = NodeManager::currentNM()->mkNode(kind::NOT,atom);
  Node negOtherAtom =  NodeManager::currentNM()->mkNode(kind::NOT,otherAtom);

  if(k == EQUAL && otherK == EQUAL){
    Assert(otherB != b);//Atoms need to be disinct
    addImplication(atom, negOtherAtom); // x == b -> x != b'
    addImplication(otherAtom, negation); // x == b' -> x != b
  }else if(k == EQUAL && otherK == LEQ){
    if(b <= otherB){
      addImplication(atom, otherAtom); // (b <= b' and x == b) -> (x <= b');
      addImplication(negOtherAtom, negation); // (b <= b' and x > b') -> (x != b);
    }else{
      addImplication(atom, negOtherAtom); // (b > b' and x == b) -> (x > b');
      addImplication(otherAtom, negation); // (b > b' and x <= b') -> x != b;
    }
  }else if(k == EQUAL && otherK == GEQ){
    if(b >= otherB){
      addImplication(atom, otherAtom); // (b >= b' and x == b) -> (x >= b');
      addImplication(negOtherAtom, negation); // (b >= b' and x < b') -> (x != b);
    }else{
      addImplication(atom, negOtherAtom); // (b < b' and x == b) -> (x < b');
      addImplication(otherAtom, negation); // (b < b' and x >= b') -> x != b;
    }
  }else if(k == LEQ && otherK == EQUAL){
    Unreachable();
  }else if(k == LEQ && otherK == LEQ){
    Assert(b.cmp(otherB) < 0);
    addImplication(atom, otherAtom); // (b < b' and x <= b) -> (x <= b');
    addImplication(negOtherAtom, negation); // (b < b' and x > b') -> (x > b);
  }else if(k == LEQ && otherK == GEQ){
    if(otherB == b){
      addImplication(negOtherAtom, atom); // (b == b' and x > b') -> (x <= b);
      addImplication(negation, otherAtom); // (b == b' and x < b') -> (x >= b);
    }else if(b < otherB){
      addImplication(atom, negOtherAtom); // (b < b' and x <= b) -> (x < b');
      addImplication(otherAtom, negation); // (b < b' and x >= b') -> (x > b);
    }else{
      addImplication(negOtherAtom, negation); // (b > b' and x < b') -> (x > b);
      addImplication(negation, otherAtom); // (b > b' and x > b) -> (x >= b');
    }
  }else if(k == GEQ && otherK == EQUAL){
    Unreachable();
  }else if(k == GEQ && otherK == LEQ){
    Unreachable();
  }else if(k == GEQ && otherK == GEQ){
    Assert(b.cmp(otherB) < 0);
    addImplication(otherAtom, atom); // (b < b' and x >= b') -> (x >= b);
    addImplication(negation, negOtherAtom); // (b < b' and x > b) -> (x > b');
  }else{
    Unreachable();
  }
}

void ArithUnatePropagator::addAtom(TNode atom){
  Assert(!atom.getAttribute(propagator::IsInPropagator()));

  Assert(isRelationOperator(atom.getKind()));

  TNode left = atom[0];
  Node negation = NodeManager::currentNM()->mkNode(kind::NOT,atom);


  d_saver.push_back(negation);

  std::vector<Node>* posImp = new std::vector<Node>();
  std::vector<Node>* negImp = new std::vector<Node>();

  atom.setAttribute(propagator::PropagatorIG(), posImp);
  negation.setAttribute(propagator::PropagatorIG(), negImp);

  std::vector<Node>* registered;
  if(!left.getAttribute(propagator::PropagatorRegisteredAtoms(), registered)){
    registered = new std::vector<Node>();
    left.setAttribute(propagator::PropagatorRegisteredAtoms(), registered);
  }

  for(std::vector<Node>::iterator i=registered->begin();
      i != registered->end(); ++i){
    TNode otherAtom = *i;

    introduceImplications(atom, otherAtom);
  }

  registered->push_back(atom);

  Debug("propagator") << atom << " " << atom.getId() << " " << negation << " " << negation.getId() << std::endl;

  atom.setAttribute(propagator::IsInPropagator(), true);
  negation.setAttribute(propagator::IsInPropagator(), true);

  Debug("propagator") << atom.getAttribute(propagator::IsInPropagator())<< " "
                      << negation.getAttribute(propagator::IsInPropagator())<< std::endl;

  Debug("propagator") << propagator::IsInPropagator().getId()<< std::endl;

}
 



void ArithUnatePropagator::assertLiteral(TNode lit){
  Assert(lit.getAttribute(propagator::IsInPropagator()));
  Assert(!lit.getAttribute(propagator::PropagatorMarked()));
  lit.setAttribute(propagator::PropagatorMarked(),true);

  d_assertions.push_back(lit);
}

std::vector<Node> ArithUnatePropagator::getImpliedLiterals(){
  std::vector<Node> impliedButNotAsserted;
  std::list<Node> newlyImplied;

  while(d_pendingAssertions < d_assertions.size()){
    Node assertion = d_assertions[d_pendingAssertions];
    newlyImplied.push_back(assertion);
    d_pendingAssertions = d_pendingAssertions + 1;
  }

  for(std::list<Node>::iterator i = newlyImplied.begin(); i != newlyImplied.end(); ++i){
    Node newAssertion = *i;
    Assert(newAssertion.hasAttribute(propagator::PropagatorIG()));
    std::vector<Node>* implied = newAssertion.getAttribute(propagator::PropagatorIG());

    for(std::vector<Node>::iterator j = implied->begin(); j != implied->end(); ++j){
      Node blah = *j;
      if(!blah.getAttribute(propagator::PropagatorMarked())){
        blah.setAttribute(propagator::PropagatorMarked(),true);
        newlyImplied.push_back(blah);
        impliedButNotAsserted.push_back(blah);

        Node explanation;
        if(newAssertion.getAttribute(propagator::PropagatorExplanation(), explanation)){
          blah.setAttribute(propagator::PropagatorExplanation(), explanation);
        }else{
          blah.setAttribute(propagator::PropagatorExplanation(), newAssertion);
        }
      }
    }
  }

  return impliedButNotAsserted;
}

Node ArithUnatePropagator::explain(TNode lit){
  Assert(lit.hasAttribute(propagator::PropagatorExplanation()));

  return lit.getAttribute(propagator::PropagatorExplanation());
}
