/*********************                                                        */
/*! \file atom_database.cpp
 ** \verbatim
 ** Original author: taking
 ** Major contributors: none
 ** Minor contributors (to current version): mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010, 2011  The Analysis of Computer Systems Group (ACSys)
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

#include "theory/arith/atom_database.h"
#include "theory/arith/arith_utilities.h"

#include <list>

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::arith;

using namespace CVC4::kind;

using namespace std;

ArithAtomDatabase::ArithAtomDatabase(context::Context* cxt, OutputChannel& out) :
  d_arithOut(out), d_setsMap()
{ }

bool ArithAtomDatabase::leftIsSetup(TNode left) const{
  return d_setsMap.find(left) != d_setsMap.end();
}

const ArithAtomDatabase::VariablesSets& ArithAtomDatabase::getVariablesSets(TNode left) const{
  Assert(leftIsSetup(left));
  NodeToSetsMap::const_iterator i = d_setsMap.find(left);
  return i->second;
}
ArithAtomDatabase::VariablesSets& ArithAtomDatabase::getVariablesSets(TNode left){
  Assert(leftIsSetup(left));
  NodeToSetsMap::iterator i = d_setsMap.find(left);
  return i->second;
}
EqualValueSet& ArithAtomDatabase::getEqualValueSet(TNode left){
  Assert(leftIsSetup(left));
  return getVariablesSets(left).d_eqValueSet;
}

const EqualValueSet& ArithAtomDatabase::getEqualValueSet(TNode left) const{
  Assert(leftIsSetup(left));
  return getVariablesSets(left).d_eqValueSet;
}

BoundValueSet& ArithAtomDatabase::getBoundValueSet(TNode left){
  Assert(leftIsSetup(left));
  return getVariablesSets(left).d_boundValueSet;
}

const BoundValueSet& ArithAtomDatabase::getBoundValueSet(TNode left) const{
  Assert(leftIsSetup(left));
  return getVariablesSets(left).d_boundValueSet;
}

bool ArithAtomDatabase::hasAnyAtoms(TNode v) const{
  Assert(!leftIsSetup(v)
         || !(getEqualValueSet(v)).empty()
         || !(getBoundValueSet(v)).empty());

  return leftIsSetup(v);
}

void ArithAtomDatabase::setupLefthand(TNode left){
  Assert(!leftIsSetup(left));

  d_setsMap[left] = VariablesSets();
}

bool ArithAtomDatabase::containsLiteral(TNode lit) const{
  switch(lit.getKind()){
  case NOT: return containsAtom(lit[0]);
  default: return containsAtom(lit);
  }
}

bool ArithAtomDatabase::containsAtom(TNode atom) const{
  switch(atom.getKind()){
  case EQUAL: return containsEquality(atom);
  case LEQ: return containsLeq(atom);
  case GEQ: return containsGeq(atom);
  default:
    Unreachable();
  }
}

bool ArithAtomDatabase::containsEquality(TNode atom) const{
  TNode left = atom[0];
  const EqualValueSet& eqSet = getEqualValueSet(left);
  return eqSet.find(atom) != eqSet.end();
}

bool ArithAtomDatabase::containsLeq(TNode atom) const{
  TNode left = atom[0];
  const Rational& value = rightHandRational(atom);

  const BoundValueSet& bvSet = getBoundValueSet(left);
  BoundValueSet::const_iterator i = bvSet.find(value);
  if(i == bvSet.end()){
    return false;
  }else{
    const BoundValueEntry& entry = i->second;
    return entry.hasLeq();
  }
}

bool ArithAtomDatabase::containsGeq(TNode atom) const{
  TNode left = atom[0];
  const Rational& value = rightHandRational(atom);

  const BoundValueSet& bvSet = getBoundValueSet(left);
  BoundValueSet::const_iterator i = bvSet.find(value);
  if(i == bvSet.end()){
    return false;
  }else{
    const BoundValueEntry& entry = i->second;
    return entry.hasGeq();
  }
}

void ArithAtomDatabase::addAtom(TNode atom){
  TNode left  = atom[0];
  TNode right = atom[1];

  if(!leftIsSetup(left)){
    setupLefthand(left);
  }

  const Rational& value = rightHandRational(atom);

  switch(atom.getKind()){
  case EQUAL:
    {
      Assert(!containsEquality(atom));
      addImplicationsUsingEqualityAndEqualityValues(atom);
      addImplicationsUsingEqualityAndBoundValues(atom);

      pair<EqualValueSet::iterator, bool> res = getEqualValueSet(left).insert(atom);
      Assert(res.second);
      break;
    }
  case LEQ:
    {
      addImplicationsUsingLeqAndEqualityValues(atom);
      addImplicationsUsingLeqAndBoundValues(atom);

      BoundValueSet& bvSet = getBoundValueSet(left);
      if(hasBoundValueEntry(atom)){
        BoundValueSet::iterator i = bvSet.find(value);
        BoundValueEntry& inSet = i->second;
        inSet.addLeq(atom);
      }else{
        bvSet.insert(make_pair(value, BoundValueEntry::mkFromLeq(atom)));
      }
      break;
    }
  case GEQ:
    {
      addImplicationsUsingGeqAndEqualityValues(atom);
      addImplicationsUsingGeqAndBoundValues(atom);

      BoundValueSet& bvSet = getBoundValueSet(left);
      if(hasBoundValueEntry(atom)){
        BoundValueSet::iterator i = bvSet.find(value);
        BoundValueEntry& inSet = i->second;
        inSet.addGeq(atom);
      }else{
        bvSet.insert(make_pair(value, BoundValueEntry::mkFromGeq(atom)));
      }
      break;
    }
  default:
    Unreachable();
  }
}

bool ArithAtomDatabase::hasBoundValueEntry(TNode atom){
  TNode left = atom[0];
  const Rational& value = rightHandRational(atom);
  BoundValueSet& bvSet = getBoundValueSet(left);
  return bvSet.find(value) != bvSet.end();
}

bool rightHandRationalIsEqual(TNode a, TNode b){
  TNode secondA = a[1];
  TNode secondB = b[1];

  const Rational& qA = secondA.getConst<Rational>();
  const Rational& qB = secondB.getConst<Rational>();

  return qA == qB;
}


bool rightHandRationalIsLT(TNode a, TNode b){
  //This version is sticking around because it is easier to read!
  return RightHandRationalLT()(a,b);
}

void ArithAtomDatabase::addImplicationsUsingEqualityAndEqualityValues(TNode atom){
  Assert(atom.getKind() == EQUAL);
  TNode left = atom[0];
  EqualValueSet& eqSet = getEqualValueSet(left);

  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  for(EqualValueSet::iterator eqIter = eqSet.begin(), endIter = eqSet.end();
      eqIter != endIter; ++eqIter){
    TNode eq = *eqIter;
    Assert(eq != atom);
    addImplication(eq, negation);
  }
}

// if weaker, do not return an equivalent node
// if strict, get the strongest bound implied by  (< x value)
// if !strict, get the strongest bound implied by  (<= x value)
Node getUpperBound(const BoundValueSet& bvSet, const Rational& value, bool strict, bool weaker){
  BoundValueSet::const_iterator bv = bvSet.lower_bound(value);
  if(bv == bvSet.end()){
    return Node::null();
  }

  if((bv->second).getValue() == value){
    const BoundValueEntry& entry = bv->second;
    if(strict && entry.hasGeq() && !weaker){
      return NodeBuilder<1>(NOT) << entry.getGeq();
    }else if(entry.hasLeq() && (strict || !weaker)){
      return entry.getLeq();
    }
  }
  ++bv;
  if(bv == bvSet.end()){
    return Node::null();
  }
  Assert(bv->second.getValue() > value);
  const BoundValueEntry& entry = bv->second;
  if(entry.hasGeq()){
    return NodeBuilder<1>(NOT) << entry.getGeq();
  }else{
    Assert(entry.hasLeq());
    return entry.getLeq();
  }
}




// if weaker, do not return an equivalent node
// if strict, get the strongest bound implied by  (> x value)
// if !strict, get the strongest bound implied by  (>= x value)
Node getLowerBound(const BoundValueSet& bvSet, const Rational& value, bool strict, bool weaker){
  static int time = 0;
  ++time;

  if(bvSet.empty()){
    return Node::null();
  }
  Debug("getLowerBound") << "getLowerBound" << bvSet.size() << " " << value << " " << strict << weaker << endl;

  BoundValueSet::const_iterator bv = bvSet.lower_bound(value);
  if(bv == bvSet.end()){
    Debug("getLowerBound") << "got end " << value << " " << (bvSet.rbegin()->second).getValue() << endl;
    Assert(value > (bvSet.rbegin()->second).getValue());
  }else{
    Debug("getLowerBound") << value << ", " << bv->second.getValue() << endl;
    Assert(value <= bv->second.getValue());
  }

  if(bv != bvSet.end() && (bv->second).getValue() == value){
    const BoundValueEntry& entry = bv->second;
    Debug("getLowerBound") << entry.hasLeq() << entry.hasGeq() << endl;
    if(strict && entry.hasLeq() && !weaker){
      return NodeBuilder<1>(NOT) << entry.getLeq();
    }else if(entry.hasGeq() && (strict || !weaker)){
      return entry.getGeq();
    }
  }
  if(bv == bvSet.begin()){
    return Node::null();
  }else{
    --bv;
    // (and (>= x v) (>= v v')) then (> x v')
    Assert(bv->second.getValue() < value);
    const BoundValueEntry& entry = bv->second;
    if(entry.hasLeq()){
      return NodeBuilder<1>(NOT) << entry.getLeq();
    }else{
      Assert(entry.hasGeq());
      return entry.getGeq();
    }
  }
}

void ArithAtomDatabase::addImplicationsUsingEqualityAndBoundValues(TNode atom){
  Assert(atom.getKind() == EQUAL);
  Node left = atom[0];

  const Rational& value = rightHandRational(atom);

  BoundValueSet& bvSet = getBoundValueSet(left);
  Node ub = getUpperBound(bvSet, value, false, false);
  Node lb = getLowerBound(bvSet, value, false, false);

  if(!ub.isNull()){
    addImplication(atom, ub);
  }

  if(!lb.isNull()){
    addImplication(atom, lb);
  }
}

void ArithAtomDatabase::addImplicationsUsingLeqAndBoundValues(TNode atom)
{
  Assert(atom.getKind() == LEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  Node ub = getImpliedUpperBoundUsingLeq(atom, false);
  Node lb = getImpliedLowerBoundUsingGT(negation, false);

  if(!ub.isNull()){
    addImplication(atom, ub);
  }

  if(!lb.isNull()){
    addImplication(negation, lb);
  }
}

void ArithAtomDatabase::addImplicationsUsingLeqAndEqualityValues(TNode atom) {
  Assert(atom.getKind() == LEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  TNode left = atom[0];
  EqualValueSet& eqSet = getEqualValueSet(left);

  //TODO Improve this later
  for(EqualValueSet::iterator eqIter = eqSet.begin(); eqIter != eqSet.end(); ++eqIter){
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


void ArithAtomDatabase::addImplicationsUsingGeqAndBoundValues(TNode atom){
  Assert(atom.getKind() == GEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);

  Node lb = getImpliedLowerBoundUsingGeq(atom, false); //What is implied by (>= left value)
  Node ub = getImpliedUpperBoundUsingLT(negation, false);

  if(!lb.isNull()){
    addImplication(atom, lb);
  }

  if(!ub.isNull()){
    addImplication(negation, ub);
  }
}
void ArithAtomDatabase::addImplicationsUsingGeqAndEqualityValues(TNode atom){

  Assert(atom.getKind() == GEQ);
  Node negation = NodeManager::currentNM()->mkNode(NOT, atom);
  Node left = atom[0];
  EqualValueSet& eqSet = getEqualValueSet(left);

  //TODO Improve this later
  for(EqualValueSet::iterator eqIter = eqSet.begin(); eqIter != eqSet.end(); ++eqIter){
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

void ArithAtomDatabase::addImplication(TNode a, TNode b){
  Node imp = NodeBuilder<2>(IMPLIES) << a << b;

  Debug("arith::unate") << "ArithAtomDatabase::addImplication"
                        << "(" << a << ", " << b <<")" << endl;

  d_arithOut.lemma(imp);
}


Node ArithAtomDatabase::getImpliedUpperBoundUsingLeq(TNode leq, bool weaker) const {
  Assert(leq.getKind() == LEQ);
  Node left = leq[0];

  if(!leftIsSetup(left)) return Node::null();

  const Rational& value = rightHandRational(leq);
  const BoundValueSet& bvSet = getBoundValueSet(left);

  Node ub = getUpperBound(bvSet, value, false, weaker);
  return ub;
}

Node ArithAtomDatabase::getImpliedUpperBoundUsingLT(TNode lt, bool weaker) const {
  Assert(lt.getKind() == NOT && lt[0].getKind() == GEQ);
  Node atom = lt[0];
  Node left = atom[0];

  if(!leftIsSetup(left)) return Node::null();

  const Rational& value = rightHandRational(atom);
  const BoundValueSet& bvSet = getBoundValueSet(left);

  return getUpperBound(bvSet, value, true, weaker);
}

Node ArithAtomDatabase::getBestImpliedUpperBound(TNode upperBound) const {
  Node result = Node::null();
  if(upperBound.getKind() == LEQ ){
    result = getImpliedUpperBoundUsingLeq(upperBound, false);
  }else if(upperBound.getKind() == NOT && upperBound[0].getKind() == GEQ){
    result = getImpliedUpperBoundUsingLT(upperBound, false);
  }else if(upperBound.getKind() == LT){
    Node geq = NodeBuilder<2>(GEQ) << upperBound[0] << upperBound[1];
    Node lt = NodeBuilder<1>(NOT) << geq;
    result = getImpliedUpperBoundUsingLT(lt, false);
  }else{
    Unreachable();
  }

  Debug("arith::unate") << upperBound <<" -> " << result << std::endl;
  return result;
}

Node ArithAtomDatabase::getWeakerImpliedUpperBound(TNode upperBound) const {
  Node result = Node::null();
  if(upperBound.getKind() == LEQ ){
    result = getImpliedUpperBoundUsingLeq(upperBound, true);
  }else if(upperBound.getKind() == NOT && upperBound[0].getKind() == GEQ){
    result = getImpliedUpperBoundUsingLT(upperBound, true);
  }else if(upperBound.getKind() == LT){
    Node geq = NodeBuilder<2>(GEQ) << upperBound[0] << upperBound[1];
    Node lt = NodeBuilder<1>(NOT) << geq;
    result = getImpliedUpperBoundUsingLT(lt, true);
  }else{
    Unreachable();
  }
  Assert(upperBound != result);
  Debug("arith::unate") << upperBound <<" -> " << result << std::endl;
  return result;
}

Node ArithAtomDatabase::getImpliedLowerBoundUsingGT(TNode gt, bool weaker) const {
  Assert(gt.getKind() == NOT && gt[0].getKind() == LEQ);
  Node atom = gt[0];
  Node left = atom[0];

  if(!leftIsSetup(left)) return Node::null();

  const Rational& value = rightHandRational(atom);
  const BoundValueSet& bvSet = getBoundValueSet(left);

  return getLowerBound(bvSet, value, true, weaker);
}

Node ArithAtomDatabase::getImpliedLowerBoundUsingGeq(TNode geq, bool weaker) const {
  Assert(geq.getKind() == GEQ);
  Node left = geq[0];

  if(!leftIsSetup(left)) return Node::null();

  const Rational& value = rightHandRational(geq);
  const BoundValueSet& bvSet = getBoundValueSet(left);

  return getLowerBound(bvSet, value, false, weaker);
}

Node ArithAtomDatabase::getBestImpliedLowerBound(TNode lowerBound) const {
  Node result = Node::null();
  if(lowerBound.getKind() == GEQ ){
    result = getImpliedLowerBoundUsingGeq(lowerBound, false);
  }else if(lowerBound.getKind() == NOT && lowerBound[0].getKind() == LEQ){
    result = getImpliedLowerBoundUsingGT(lowerBound, false);
  }else if(lowerBound.getKind() == GT){
    Node leq = NodeBuilder<2>(LEQ)<<lowerBound[0]<< lowerBound[1];
    Node gt = NodeBuilder<1>(NOT) << leq;
    result = getImpliedLowerBoundUsingGT(gt, false);
  }else{
    Unreachable();
  }
  Debug("arith::unate") << lowerBound <<" -> " << result << std::endl;
  return result;
}

Node ArithAtomDatabase::getWeakerImpliedLowerBound(TNode lowerBound) const {
  Node result = Node::null();
  if(lowerBound.getKind() == GEQ ){
    result = getImpliedLowerBoundUsingGeq(lowerBound, true);
  }else if(lowerBound.getKind() == NOT && lowerBound[0].getKind() == LEQ){
    result = getImpliedLowerBoundUsingGT(lowerBound, true);
  }else if(lowerBound.getKind() == GT){
    Node leq = NodeBuilder<2>(LEQ)<<lowerBound[0]<< lowerBound[1];
    Node gt = NodeBuilder<1>(NOT) << leq;
    result = getImpliedLowerBoundUsingGT(gt, true);
  }else{
    Unreachable();
  }
  Assert(result != lowerBound);

  Debug("arith::unate") << lowerBound <<" -> " << result << std::endl;
  return result;
}
