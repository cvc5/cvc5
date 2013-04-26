/*********************                                                        */
/*! \file constraint.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"
#include "theory/arith/constraint.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/normal_form.h"

#include <ostream>
#include <algorithm>

using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

/** Given a simplifiedKind this returns the corresponding ConstraintType. */
//ConstraintType constraintTypeOfLiteral(Kind k);
ConstraintType constraintTypeOfComparison(const Comparison& cmp){
  Kind k = cmp.comparisonKind();
  switch(k){
  case LT:
  case LEQ:
    {
      Polynomial l = cmp.getLeft();
      if(l.leadingCoefficientIsPositive()){ // (< x c)
        return UpperBound;
      }else{
        return LowerBound; // (< (-x) c)
      }
    }
  case GT:
  case GEQ:
    {
      Polynomial l = cmp.getLeft();
      if(l.leadingCoefficientIsPositive()){
        return LowerBound; // (> x c)
      }else{
        return UpperBound; // (> (-x) c)
      }
    }
  case EQUAL:
    return Equality;
  case DISTINCT:
    return Disequality;
  default:
    Unhandled(k);
  }
}

ConstraintValue::ConstraintValue(ArithVar x,  ConstraintType t, const DeltaRational& v)
  : d_variable(x),
    d_type(t),
    d_value(v),
    d_database(NULL),
    d_literal(Node::null()),
    d_negation(NullConstraint),
    d_canBePropagated(false),
    _d_assertionOrder(AssertionOrderSentinel),
    d_witness(TNode::null()),
    d_proof(ProofIdSentinel),
    d_split(false),
    d_variablePosition()
{
  Assert(!initialized());
}


std::ostream& operator<<(std::ostream& o, const Constraint c){
  if(c == NullConstraint){
    return o << "NullConstraint";
  }else{
    return o << *c;
  }
}

std::ostream& operator<<(std::ostream& o, const ConstraintType t){
  switch(t){
  case LowerBound:
    return o << ">=";
  case UpperBound:
    return o << "<=";
  case Equality:
    return o << "=";
  case Disequality:
    return o << "!=";
  default:
    Unreachable();
  }
}

std::ostream& operator<<(std::ostream& o, const ConstraintValue& c){
  o << c.getVariable() << ' ' << c.getType() << ' ' << c.getValue();
  if(c.hasLiteral()){
    o << "(node " << c.getLiteral() << ')';
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const ValueCollection& vc){
  o << "{";
  bool pending = false;
  if(vc.hasEquality()){
    o << "eq: " << vc.getEquality();
    pending = true;
  }
  if(vc.hasLowerBound()){
    if(pending){
      o << ", ";
    }
    o << "lb: " << vc.getLowerBound();
    pending = true;
  }
  if(vc.hasUpperBound()){
    if(pending){
      o << ", ";
    }
    o << "ub: " << vc.getUpperBound();
    pending = true;
  }
  if(vc.hasDisequality()){
    if(pending){
      o << ", ";
    }
    o << "de: " << vc.getDisequality();
  }
  return o << "}";
}

void ConstraintValue::debugPrint() const {
  Message() << *this << endl;
}

void ValueCollection::push_into(std::vector<Constraint>& vec) const {
  Debug("arith::constraint") << "push_into " << *this << endl;
  if(hasEquality()){
    vec.push_back(d_equality);
  }
  if(hasLowerBound()){
    vec.push_back(d_lowerBound);
  }
  if(hasUpperBound()){
    vec.push_back(d_upperBound);
  }
  if(hasDisequality()){
    vec.push_back(d_disequality);
  }
}

ValueCollection ValueCollection::mkFromConstraint(Constraint c){
  ValueCollection ret;
  Assert(ret.empty());
  switch(c->getType()){
  case LowerBound:
    ret.d_lowerBound = c;
    break;
  case UpperBound:
    ret.d_upperBound = c;
    break;
  case Equality:
    ret.d_equality = c;
    break;
  case Disequality:
    ret.d_disequality = c;
    break;
  default:
    Unreachable();
  }
  return ret;
}

bool ValueCollection::hasConstraintOfType(ConstraintType t) const{
  switch(t){
  case LowerBound:
    return hasLowerBound();
  case UpperBound:
    return hasUpperBound();
  case Equality:
    return hasEquality();
  case Disequality:
    return hasDisequality();
  default:
    Unreachable();
  }
}

ArithVar ValueCollection::getVariable() const{
  Assert(!empty());
  return nonNull()->getVariable();
}

const DeltaRational& ValueCollection::getValue() const{
  Assert(!empty());
  return nonNull()->getValue();
}

void ValueCollection::add(Constraint c){
  Assert(c != NullConstraint);

  Assert(empty() || getVariable() == c->getVariable());
  Assert(empty() || getValue() == c->getValue());

  switch(c->getType()){
  case LowerBound:
    Assert(!hasLowerBound());
    d_lowerBound = c;
    break;
  case Equality:
    Assert(!hasEquality());
    d_equality = c;
    break;
  case UpperBound:
    Assert(!hasUpperBound());
    d_upperBound = c;
    break;
  case Disequality:
    Assert(!hasDisequality());
    d_disequality = c;
    break;
  default:
    Unreachable();
  }
}

Constraint ValueCollection::getConstraintOfType(ConstraintType t) const{
  switch(t){
  case LowerBound:
    Assert(hasLowerBound());
    return d_lowerBound;
  case Equality:
    Assert(hasEquality());
    return d_equality;
  case UpperBound:
    Assert(hasUpperBound());
    return d_upperBound;
  case Disequality:
    Assert(hasDisequality());
    return d_disequality;
  default:
    Unreachable();
  }
}

void ValueCollection::remove(ConstraintType t){
  switch(t){
  case LowerBound:
    Assert(hasLowerBound());
    d_lowerBound = NullConstraint;
    break;
  case Equality:
    Assert(hasEquality());
    d_equality = NullConstraint;
    break;
  case UpperBound:
    Assert(hasUpperBound());
    d_upperBound = NullConstraint;
    break;
  case Disequality:
    Assert(hasDisequality());
    d_disequality = NullConstraint;
    break;
  default:
    Unreachable();
  }
}

bool ValueCollection::empty() const{
  return
    !(hasLowerBound() ||
      hasUpperBound() ||
      hasEquality() ||
      hasDisequality());
}

Constraint ValueCollection::nonNull() const{
  //This can be optimized by caching, but this is not necessary yet!
  /* "Premature optimization is the root of all evil." */
  if(hasLowerBound()){
    return d_lowerBound;
  }else if(hasUpperBound()){
    return d_upperBound;
  }else if(hasEquality()){
    return d_equality;
  }else if(hasDisequality()){
    return d_disequality;
  }else{
    return NullConstraint;
  }
}

bool ConstraintValue::initialized() const {
  return d_database != NULL;
}

void ConstraintValue::initialize(ConstraintDatabase* db, SortedConstraintMapIterator v, Constraint negation){
  Assert(!initialized());
  d_database = db;
  d_variablePosition = v;
  d_negation = negation;
}

ConstraintValue::~ConstraintValue() {
  Assert(safeToGarbageCollect());

  if(initialized()){
    ValueCollection& vc =  d_variablePosition->second;
    Debug("arith::constraint") << "removing" << vc << endl;

    vc.remove(getType());

    if(vc.empty()){
      Debug("arith::constraint") << "erasing" << vc << endl;
      SortedConstraintMap& perVariable = d_database->getVariableSCM(getVariable());
      perVariable.erase(d_variablePosition);
    }

    if(hasLiteral()){
      d_database->d_nodetoConstraintMap.erase(getLiteral());
    }
  }
}

const ValueCollection& ConstraintValue::getValueCollection() const{
  return d_variablePosition->second;
}

Constraint ConstraintValue::getCeiling() {
  Debug("getCeiling") << "ConstraintValue::getCeiling on " << *this << endl;
  Assert(getValue().getInfinitesimalPart().sgn() > 0);

  DeltaRational ceiling(getValue().ceiling());

  // TODO: "Optimize via the iterator"
  return d_database->getConstraint(getVariable(), getType(), ceiling);
}

Constraint ConstraintValue::getFloor() {
  Assert(getValue().getInfinitesimalPart().sgn() < 0);

  DeltaRational floor(Rational(getValue().floor()));

  // TODO: "Optimize via the iterator"
  return d_database->getConstraint(getVariable(), getType(), floor);
}

void ConstraintValue::setCanBePropagated() {
  Assert(!canBePropagated());
  d_database->pushCanBePropagatedWatch(this);
}

void ConstraintValue::setAssertedToTheTheory(TNode witness) {
  Assert(hasLiteral());
  Assert(!assertedToTheTheory());
  Assert(!d_negation->assertedToTheTheory());
  d_database->pushAssertionOrderWatch(this, witness);
}

bool ConstraintValue::satisfiedBy(const DeltaRational& dr) const {
  switch(getType()){
  case LowerBound:
    return getValue() <= dr;
  case Equality:
    return getValue() == dr;
  case UpperBound:
    return getValue() >= dr;
  case Disequality:
    return getValue() != dr;
  }
  Unreachable();
}

// bool ConstraintValue::isPsuedoConstraint() const {
//   return d_proof == d_database->d_psuedoConstraintProof;
// }

bool ConstraintValue::isSelfExplaining() const {
  return d_proof == d_database->d_selfExplainingProof;
}

bool ConstraintValue::hasEqualityEngineProof() const {
  return d_proof == d_database->d_equalityEngineProof;
}

bool ConstraintValue::sanityChecking(Node n) const {
  Comparison cmp = Comparison::parseNormalForm(n);
  Kind k = cmp.comparisonKind();
  Polynomial pleft = cmp.normalizedVariablePart();
  Assert(k == EQUAL || k == DISTINCT || pleft.leadingCoefficientIsPositive());
  Assert(k != EQUAL || Monomial::isMember(n[0]));
  Assert(k != DISTINCT || Monomial::isMember(n[0][0]));

  TNode left = pleft.getNode();
  DeltaRational right = cmp.normalizedDeltaRational();

  const ArithVariables& avariables = d_database->getArithVariables();

  Debug("nf::tmp") << cmp.getNode() << endl;
  Debug("nf::tmp") << k << endl;
  Debug("nf::tmp") << pleft.getNode() << endl;
  Debug("nf::tmp") << left << endl;
  Debug("nf::tmp") << right << endl;
  Debug("nf::tmp") << getValue() << endl;
  Debug("nf::tmp") << avariables.hasArithVar(left) << endl;
  Debug("nf::tmp") << avariables.asArithVar(left) << endl;
  Debug("nf::tmp") << getVariable() << endl;


  if(avariables.hasArithVar(left) &&
     avariables.asArithVar(left) == getVariable() &&
     getValue() == right){
    switch(getType()){
    case LowerBound:
    case UpperBound:
      //Be overapproximate
      return k == GT || k == GEQ ||k == LT || k == LEQ;
    case Equality:
      return k == EQUAL;
    case Disequality:
      return k == DISTINCT;
    default:
      Unreachable();
    }
  }else{
    return false;
  }
}

Constraint ConstraintValue::makeNegation(ArithVar v, ConstraintType t, const DeltaRational& r){
  switch(t){
  case LowerBound:
    {
      Assert(r.infinitesimalSgn() >= 0);
      if(r.infinitesimalSgn() > 0){
        Assert(r.getInfinitesimalPart() == 1);
        // make (not (v > r)), which is (v <= r)
        DeltaRational dropInf(r.getNoninfinitesimalPart(), 0);
        return new ConstraintValue(v, UpperBound, dropInf);
      }else{
        Assert(r.infinitesimalSgn() == 0);
        // make (not (v >= r)), which is (v < r)
        DeltaRational addInf(r.getNoninfinitesimalPart(), -1);
        return new ConstraintValue(v, UpperBound, addInf);
      }
    }
  case UpperBound:
    {
      Assert(r.infinitesimalSgn() <= 0);
      if(r.infinitesimalSgn() < 0){
        Assert(r.getInfinitesimalPart() == -1);
        // make (not (v < r)), which is (v >= r)
        DeltaRational dropInf(r.getNoninfinitesimalPart(), 0);
        return new ConstraintValue(v, LowerBound, dropInf);
      }else{
        Assert(r.infinitesimalSgn() == 0);
        // make (not (v <= r)), which is (v > r)
        DeltaRational addInf(r.getNoninfinitesimalPart(), 1);
        return new ConstraintValue(v, LowerBound, addInf);
      }
    }
  case Equality:
    return new ConstraintValue(v, Disequality, r);
  case Disequality:
    return new ConstraintValue(v, Equality, r);
  default:
    Unreachable();
    return NullConstraint;
  }
}

ConstraintDatabase::ConstraintDatabase(context::Context* satContext, context::Context* userContext, const ArithVariables& avars, ArithCongruenceManager& cm, RaiseConflict raiseConflict)
  : d_varDatabases(),
    d_toPropagate(satContext),
    d_proofs(satContext, false),
    d_watches(new Watches(satContext, userContext)),
    d_avariables(avars),
    d_congruenceManager(cm),
    d_satContext(satContext),
    d_satAllocationLevel(d_satContext->getLevel()),
    d_raiseConflict(raiseConflict)
{
  d_selfExplainingProof = d_proofs.size();
  d_proofs.push_back(NullConstraint);

  d_equalityEngineProof = d_proofs.size();
  d_proofs.push_back(NullConstraint);

  // d_pseudoConstraintProof = d_proofs.size();
  // d_proofs.push_back(NullConstraint);
}

Constraint ConstraintDatabase::getConstraint(ArithVar v, ConstraintType t, const DeltaRational& r){
  //This must always return a constraint.

  SortedConstraintMap& scm = getVariableSCM(v);
  pair<SortedConstraintMapIterator, bool> insertAttempt;
  insertAttempt = scm.insert(make_pair(r, ValueCollection()));

  SortedConstraintMapIterator pos = insertAttempt.first;
  ValueCollection& vc = pos->second;
  if(vc.hasConstraintOfType(t)){
    return vc.getConstraintOfType(t);
  }else{
    Constraint c = new ConstraintValue(v, t, r);
    Constraint negC = ConstraintValue::makeNegation(v, t, r);

    SortedConstraintMapIterator negPos;
    if(t == Equality || t == Disequality){
      negPos = pos;
    }else{
      pair<SortedConstraintMapIterator, bool> negInsertAttempt;
      negInsertAttempt = scm.insert(make_pair(negC->getValue(), ValueCollection()));
      Assert(negInsertAttempt.second
             || ! negInsertAttempt.first->second.hasConstraintOfType(negC->getType()));
      negPos = negInsertAttempt.first;
    }

    c->initialize(this, pos, negC);
    negC->initialize(this, negPos, c);

    vc.add(c);
    negPos->second.add(negC);

    return c;
  }
}
bool ConstraintDatabase::emptyDatabase(const std::vector<PerVariableDatabase>& vec){
  std::vector<PerVariableDatabase>::const_iterator first = vec.begin();
  std::vector<PerVariableDatabase>::const_iterator last = vec.end();
  return std::find_if(first, last, PerVariableDatabase::IsEmpty) == last;
}

ConstraintDatabase::~ConstraintDatabase(){
  Assert(d_satAllocationLevel <= d_satContext->getLevel());

  delete d_watches;

  std::vector<Constraint> constraintList;

  while(!d_varDatabases.empty()){
    PerVariableDatabase* back = d_varDatabases.back();

    SortedConstraintMap& scm = back->d_constraints;
    SortedConstraintMapIterator i = scm.begin(), i_end = scm.end();
    for(; i != i_end; ++i){
      (i->second).push_into(constraintList);
    }
    while(!constraintList.empty()){
      Constraint c = constraintList.back();
      constraintList.pop_back();
      delete c;
    }
    Assert(scm.empty());
    d_varDatabases.pop_back();
    delete back;
  }

  Assert(d_nodetoConstraintMap.empty());
}

ConstraintDatabase::Statistics::Statistics():
  d_unatePropagateCalls("theory::arith::cd::unatePropagateCalls", 0),
  d_unatePropagateImplications("theory::arith::cd::unatePropagateImplications", 0)
{
  StatisticsRegistry::registerStat(&d_unatePropagateCalls);
  StatisticsRegistry::registerStat(&d_unatePropagateImplications);

}
ConstraintDatabase::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_unatePropagateCalls);
  StatisticsRegistry::unregisterStat(&d_unatePropagateImplications);
}

void ConstraintDatabase::addVariable(ArithVar v){
  if(d_reclaimable.isMember(v)){
    SortedConstraintMap& scm = getVariableSCM(v);

    std::vector<Constraint> constraintList;

    for(SortedConstraintMapIterator i = scm.begin(), end = scm.end(); i != end; ++i){
      (i->second).push_into(constraintList);
    }
    while(!constraintList.empty()){
      Constraint c = constraintList.back();
      constraintList.pop_back();
      Assert(c->safeToGarbageCollect());
      delete c;
    }
    Assert(scm.empty());

    d_reclaimable.remove(v);
  }else{
    Assert(v == d_varDatabases.size());
    d_varDatabases.push_back(new PerVariableDatabase(v));
  }
}

void ConstraintDatabase::removeVariable(ArithVar v){
  Assert(!d_reclaimable.isMember(v));
  d_reclaimable.add(v);
}

bool ConstraintValue::safeToGarbageCollect() const{
  return !isSplit()
    && !canBePropagated()
    && !hasProof()
    && !assertedToTheTheory();
}

Node ConstraintValue::split(){
  Assert(isEquality() || isDisequality());

  bool isEq = isEquality();

  Constraint eq = isEq ? this : d_negation;
  Constraint diseq = isEq ? d_negation : this;

  TNode eqNode = eq->getLiteral();
  Assert(eqNode.getKind() == kind::EQUAL);
  TNode lhs = eqNode[0];
  TNode rhs = eqNode[1];

  Node leqNode = NodeBuilder<2>(kind::LEQ) << lhs << rhs;
  Node geqNode = NodeBuilder<2>(kind::GEQ) << lhs << rhs;

  Node lemma = NodeBuilder<3>(OR) << leqNode << geqNode;


  eq->d_database->pushSplitWatch(eq);
  diseq->d_database->pushSplitWatch(diseq);

  return lemma;
}

bool ConstraintDatabase::hasLiteral(TNode literal) const {
  return lookup(literal) != NullConstraint;
}

// Constraint ConstraintDatabase::addLiteral(TNode literal){
//   Assert(!hasLiteral(literal));
//   bool isNot = (literal.getKind() == NOT);
//   TNode atom = isNot ? literal[0] : literal;

//   Constraint atomC = addAtom(atom);

//   return isNot ? atomC->d_negation : atomC;
// }

// Constraint ConstraintDatabase::allocateConstraintForComparison(ArithVar v, const Comparison cmp){
//   Debug("arith::constraint") << "allocateConstraintForLiteral(" << v << ", "<< cmp <<")" << endl;
//   Kind kind = cmp.comparisonKind();
//   ConstraintType type = constraintTypeOfLiteral(kind);
  
//   DeltaRational dr = cmp.getDeltaRational();
//   return new ConstraintValue(v, type, dr);
// }

Constraint ConstraintDatabase::addLiteral(TNode literal){
  Assert(!hasLiteral(literal));
  bool isNot = (literal.getKind() == NOT);
  Node atomNode = (isNot ? literal[0] : literal);
  Node negationNode  = atomNode.notNode();

  Assert(!hasLiteral(atomNode));
  Assert(!hasLiteral(negationNode));
  Comparison posCmp = Comparison::parseNormalForm(atomNode);

  ConstraintType posType = constraintTypeOfComparison(posCmp);

  Polynomial nvp = posCmp.normalizedVariablePart();
  Debug("nf::tmp") << "here " <<  nvp.getNode() << " " << endl;
  ArithVar v = d_avariables.asArithVar(nvp.getNode());

  DeltaRational posDR = posCmp.normalizedDeltaRational();

  Constraint posC = new ConstraintValue(v, posType, posDR);

  Debug("arith::constraint") << "addliteral( literal ->" << literal << ")" << endl;
  Debug("arith::constraint") << "addliteral( posC ->" << posC << ")" << endl;

  SortedConstraintMap& scm = getVariableSCM(posC->getVariable());
  pair<SortedConstraintMapIterator, bool> insertAttempt;
  insertAttempt = scm.insert(make_pair(posC->getValue(), ValueCollection()));

  SortedConstraintMapIterator posI = insertAttempt.first;
  // If the attempt succeeds, i points to a new empty ValueCollection
  // If the attempt fails, i points to a pre-existing ValueCollection

  if(posI->second.hasConstraintOfType(posC->getType())){
    //This is the situation where the Constraint exists, but
    //the literal has not been  associated with it.
    Constraint hit = posI->second.getConstraintOfType(posC->getType());
    Debug("arith::constraint") << "hit " << hit << endl;
    Debug("arith::constraint") << "posC " << posC << endl;

    delete posC;

    hit->setLiteral(atomNode);
    hit->getNegation()->setLiteral(negationNode);
    return isNot ? hit->getNegation(): hit;
  }else{
    Comparison negCmp = Comparison::parseNormalForm(negationNode);
    
    ConstraintType negType = constraintTypeOfComparison(negCmp);
    DeltaRational negDR = negCmp.normalizedDeltaRational();

    Constraint negC = new ConstraintValue(v, negType, negDR);

    SortedConstraintMapIterator negI;

    if(posC->isEquality()){
      negI = posI;
    }else{
      Assert(posC->isLowerBound() || posC->isUpperBound());

      pair<SortedConstraintMapIterator, bool> negInsertAttempt;
      negInsertAttempt = scm.insert(make_pair(negC->getValue(), ValueCollection()));

      Debug("nf::tmp") << "sdhjfgdhjkldfgljkhdfg" << endl;
      Debug("nf::tmp") << negC << endl;
      Debug("nf::tmp") << negC->getValue() << endl;

      //This should always succeed as the DeltaRational for the negation is unique!
      Assert(negInsertAttempt.second);

      negI = negInsertAttempt.first;
    }

    (posI->second).add(posC);
    (negI->second).add(negC);

    posC->initialize(this, posI, negC);
    negC->initialize(this, negI, posC);

    posC->setLiteral(atomNode);
    negC->setLiteral(negationNode);

    return isNot ? negC : posC;
  }
}

// ConstraintType constraintTypeOfLiteral(Kind k){
//   switch(k){
//   case LT:
//   case LEQ:
//     return UpperBound;
//   case GT:
//   case GEQ:
//     return LowerBound;
//   case EQUAL:
//     return Equality;
//   case DISTINCT:
//     return Disequality;
//   default:
//     Unreachable();
//   }
// }

Constraint ConstraintDatabase::lookup(TNode literal) const{
  NodetoConstraintMap::const_iterator iter = d_nodetoConstraintMap.find(literal);
  if(iter == d_nodetoConstraintMap.end()){
    return NullConstraint;
  }else{
    return iter->second;
  }
}

void ConstraintValue::selfExplaining(){
  markAsTrue();
}

void ConstraintValue::propagate(){
  Assert(hasProof());
  Assert(canBePropagated());
  Assert(!assertedToTheTheory());
  Assert(!isSelfExplaining());

  d_database->d_toPropagate.push(this);
}

void ConstraintValue::propagate(Constraint a){
  Assert(!hasProof());
  Assert(canBePropagated());

  markAsTrue(a);
  propagate();
}

void ConstraintValue::propagate(Constraint a, Constraint b){
  Assert(!hasProof());
  Assert(canBePropagated());

  markAsTrue(a, b);
  propagate();
}

void ConstraintValue::propagate(const std::vector<Constraint>& b){
  Assert(!hasProof());
  Assert(canBePropagated());

  markAsTrue(b);
  propagate();
}

void ConstraintValue::impliedBy(Constraint a){
  Assert(!isTrue());
  Assert(!getNegation()->isTrue());

  markAsTrue(a);
  if(canBePropagated()){
    propagate();
  }
}

void ConstraintValue::impliedBy(Constraint a, Constraint b){
  Assert(!isTrue());
  Assert(!getNegation()->isTrue());

  markAsTrue(a, b);
  if(canBePropagated()){
    propagate();
  }
}

void ConstraintValue::impliedBy(const std::vector<Constraint>& b){
  Assert(!isTrue());
  Assert(!getNegation()->isTrue());

  markAsTrue(b);
  if(canBePropagated()){
    propagate();
  }
}

// void ConstraintValue::setPseudoConstraint(){
//   Assert(truthIsUnknown());
//   Assert(!hasLiteral());

//   d_database->pushProofWatch(this, d_database->d_pseudoConstraintProof);
// }

void ConstraintValue::setEqualityEngineProof(){
  Assert(truthIsUnknown());
  Assert(hasLiteral());
  d_database->pushProofWatch(this, d_database->d_equalityEngineProof);
}

void ConstraintValue::markAsTrue(){
  Assert(truthIsUnknown());
  Assert(hasLiteral());
  Assert(assertedToTheTheory());
  d_database->pushProofWatch(this, d_database->d_selfExplainingProof);
}

void ConstraintValue::markAsTrue(Constraint imp){
  Assert(truthIsUnknown());
  Assert(imp->hasProof());
  //Assert(!imp->isPseudoConstraint());

  d_database->d_proofs.push_back(NullConstraint);
  d_database->d_proofs.push_back(imp);
  ProofId proof = d_database->d_proofs.size() - 1;
  d_database->pushProofWatch(this, proof);
}

void ConstraintValue::markAsTrue(Constraint impA, Constraint impB){
  Assert(truthIsUnknown());
  Assert(impA->hasProof());
  Assert(impB->hasProof());
  //Assert(!impA->isPseudoConstraint());
  //Assert(!impB->isPseudoConstraint());

  d_database->d_proofs.push_back(NullConstraint);
  d_database->d_proofs.push_back(impA);
  d_database->d_proofs.push_back(impB);
  ProofId proof = d_database->d_proofs.size() - 1;

  d_database->pushProofWatch(this, proof);
}

void ConstraintValue::markAsTrue(const vector<Constraint>& a){
  Assert(truthIsUnknown());
  Assert(a.size() >= 1);
  d_database->d_proofs.push_back(NullConstraint);
  for(vector<Constraint>::const_iterator i = a.begin(), end = a.end(); i != end; ++i){
    Constraint c_i = *i;
    Assert(c_i->hasProof());
    //Assert(!c_i->isPseudoConstraint());
    d_database->d_proofs.push_back(c_i);
  }

  ProofId proof = d_database->d_proofs.size() - 1;

  d_database->pushProofWatch(this, proof);
}

SortedConstraintMap& ConstraintValue::constraintSet() const{
  Assert(d_database->variableDatabaseIsSetup(d_variable));
  return (d_database->d_varDatabases[d_variable])->d_constraints;
}

bool ConstraintValue::proofIsEmpty() const{
  Assert(hasProof());
  bool result = d_database->d_proofs[d_proof] == NullConstraint;
  //Assert((!result) || isSelfExplaining() || hasEqualityEngineProof() || isPseudoConstraint());
  Assert((!result) || isSelfExplaining() || hasEqualityEngineProof());
  return result;
}

void ConstraintValue::explainBefore(NodeBuilder<>& nb, AssertionOrder order) const{
  Assert(hasProof());
  Assert(!isSelfExplaining() || assertedToTheTheory());


  if(assertedBefore(order)){
    nb << getWitness();
  }else if(hasEqualityEngineProof()){
    d_database->eeExplain(this, nb);
  }else{
    Assert(!isSelfExplaining());
    ProofId p = d_proof;
    Constraint antecedent = d_database->d_proofs[p];

    for(; antecedent != NullConstraint; antecedent = d_database->d_proofs[--p] ){
      antecedent->explainBefore(nb, order);
    }
  }
}
Node ConstraintValue::explainBefore(AssertionOrder order) const{
  Assert(hasProof());
  Assert(!isSelfExplaining() || assertedBefore(order));
  if(assertedBefore(order)){
    return getWitness();
  }else if(hasEqualityEngineProof()){
    return d_database->eeExplain(this);
  }else{
    Assert(!proofIsEmpty());
    //Force the selection of the layer above if the node is assertedToTheTheory()!
    if(d_database->d_proofs[d_proof-1] == NullConstraint){
      Constraint antecedent = d_database->d_proofs[d_proof];
      return antecedent->explainBefore(order);
    }else{
      NodeBuilder<> nb(kind::AND);
      Assert(!isSelfExplaining());

      ProofId p = d_proof;
      Constraint antecedent = d_database->d_proofs[p];
      for(; antecedent != NullConstraint; antecedent = d_database->d_proofs[--p] ){
        antecedent->explainBefore(nb, order);
      }
      return nb;
    }
  }
}

Node ConstraintValue::explainConflict(Constraint a, Constraint b){
  NodeBuilder<> nb(kind::AND);
  a->explainForConflict(nb);
  b->explainForConflict(nb);
  return nb;
}

Node ConstraintValue::explainConflict(Constraint a, Constraint b, Constraint c){
  NodeBuilder<> nb(kind::AND);
  a->explainForConflict(nb);
  b->explainForConflict(nb);
  c->explainForConflict(nb);
  return nb;
}

Constraint ConstraintValue::getStrictlyWeakerLowerBound(bool hasLiteral, bool asserted) const {
  Assert(initialized());
  Assert(!asserted || hasLiteral);

  SortedConstraintMapConstIterator i = d_variablePosition;
  const SortedConstraintMap& scm = constraintSet();
  SortedConstraintMapConstIterator i_begin = scm.begin();
  while(i != i_begin){
    --i;
    const ValueCollection& vc = i->second;
    if(vc.hasLowerBound()){
      Constraint weaker = vc.getLowerBound();

      // asserted -> hasLiteral
      // hasLiteral -> weaker->hasLiteral()
      // asserted -> weaker->assertedToTheTheory()
      if((!hasLiteral || (weaker->hasLiteral())) &&
         (!asserted || ( weaker->assertedToTheTheory()))){
        return weaker;
      }
    }
  }
  return NullConstraint;
}

Constraint ConstraintValue::getStrictlyWeakerUpperBound(bool hasLiteral, bool asserted) const {
  SortedConstraintMapConstIterator i = d_variablePosition;
  const SortedConstraintMap& scm = constraintSet();
  SortedConstraintMapConstIterator i_end = scm.end();

  ++i;
  for(; i != i_end; ++i){
    const ValueCollection& vc = i->second;
    if(vc.hasUpperBound()){
      Constraint weaker = vc.getUpperBound();
      if((!hasLiteral || (weaker->hasLiteral())) &&
         (!asserted || ( weaker->assertedToTheTheory()))){
        return weaker;
      }
    }
  }

  return NullConstraint;
}

Constraint ConstraintDatabase::getBestImpliedBound(ArithVar v, ConstraintType t, const DeltaRational& r) const {
  Assert(variableDatabaseIsSetup(v));
  Assert(t == UpperBound ||  t == LowerBound);

  SortedConstraintMap& scm = getVariableSCM(v);
  if(t == UpperBound){
    SortedConstraintMapConstIterator i = scm.lower_bound(r);
    SortedConstraintMapConstIterator i_end = scm.end();
    Assert(i == i_end || r <= i->first);
    for(; i != i_end; i++){
      Assert(r <= i->first);
      const ValueCollection& vc = i->second;
      if(vc.hasUpperBound()){
        return vc.getUpperBound();
      }
    }
    return NullConstraint;
  }else{
    Assert(t == LowerBound);
    if(scm.empty()){
      return NullConstraint;
    }else{
      SortedConstraintMapConstIterator i = scm.lower_bound(r);
      SortedConstraintMapConstIterator i_begin = scm.begin();
      SortedConstraintMapConstIterator i_end = scm.end();
      Assert(i == i_end || r <= i->first);

      int fdj = 0;

      if(i == i_end){
        --i;
        Debug("getBestImpliedBound") << fdj++ << " " << r << " " << i->first << endl;
      }else if( (i->first) > r){
        if(i == i_begin){
          return NullConstraint;
        }else{
          --i;
          Debug("getBestImpliedBound") << fdj++ << " " << r << " " << i->first << endl;
        }
      }

      do{
        Debug("getBestImpliedBound") << fdj++ << " " << r << " " << i->first << endl;
        Assert(r >= i->first);
        const ValueCollection& vc = i->second;

        if(vc.hasLowerBound()){
          return vc.getLowerBound();
        }

        if(i == i_begin){
          break;
        }else{
          --i;
        }
      }while(true);
      return NullConstraint;
    }
  }
}
Node ConstraintDatabase::eeExplain(const ConstraintValue* const c) const{
  Assert(c->hasLiteral());
  return d_congruenceManager.explain(c->getLiteral());
}

void ConstraintDatabase::eeExplain(const ConstraintValue* const c, NodeBuilder<>& nb) const{
  Assert(c->hasLiteral());
  d_congruenceManager.explain(c->getLiteral(), nb);
}

bool ConstraintDatabase::variableDatabaseIsSetup(ArithVar v) const {
  return v < d_varDatabases.size();
}


ConstraintDatabase::Watches::Watches(context::Context* satContext, context::Context* userContext):
  d_proofWatches(satContext),
  d_canBePropagatedWatches(satContext),
  d_assertionOrderWatches(satContext),
  d_splitWatches(userContext)
{}


void ConstraintValue::setLiteral(Node n) {
  Assert(!hasLiteral());
  Assert(sanityChecking(n));
  d_literal = n;
  NodetoConstraintMap& map = d_database->d_nodetoConstraintMap;
  Assert(map.find(n) == map.end());
  map.insert(make_pair(d_literal, this));
}

void implies(std::vector<Node>& out, Constraint a, Constraint b){
  Node la = a->getLiteral();
  Node lb = b->getLiteral();

  Node neg_la = (la.getKind() == kind::NOT)? la[0] : la.notNode();

  Assert(lb != neg_la);
  Node orderOr = (lb < neg_la) ? lb.orNode(neg_la) : neg_la.orNode(lb);
  out.push_back(orderOr);
}

void mutuallyExclusive(std::vector<Node>& out, Constraint a, Constraint b){
  Node la = a->getLiteral();
  Node lb = b->getLiteral();

  Node neg_la = (la.getKind() == kind::NOT)? la[0] : la.notNode();
  Node neg_lb = (lb.getKind() == kind::NOT)? lb[0] : lb.notNode();

  Assert(neg_la != neg_lb);
  Node orderOr = (neg_la < neg_lb) ? neg_la.orNode(neg_lb) : neg_lb.orNode(neg_la);
  out.push_back(orderOr);
}

void ConstraintDatabase::outputUnateInequalityLemmas(std::vector<Node>& out, ArithVar v) const{
  SortedConstraintMap& scm = getVariableSCM(v);
  SortedConstraintMapConstIterator scm_iter = scm.begin();
  SortedConstraintMapConstIterator scm_end = scm.end();
  Constraint prev = NullConstraint;
  //get transitive unates
  //Only lower bounds or upperbounds should be done.
  for(; scm_iter != scm_end; ++scm_iter){
    const ValueCollection& vc = scm_iter->second;
    if(vc.hasUpperBound()){
      Constraint ub = vc.getUpperBound();
      if(ub->hasLiteral()){
        if(prev != NullConstraint){
          implies(out, prev, ub);
        }
        prev = ub;
      }
    }
  }
}

void ConstraintDatabase::outputUnateEqualityLemmas(std::vector<Node>& out, ArithVar v) const{

  vector<Constraint> equalities;

  SortedConstraintMap& scm = getVariableSCM(v);
  SortedConstraintMapConstIterator scm_iter = scm.begin();
  SortedConstraintMapConstIterator scm_end = scm.end();

  for(; scm_iter != scm_end; ++scm_iter){
    const ValueCollection& vc = scm_iter->second;
    if(vc.hasEquality()){
      Constraint eq = vc.getEquality();
      if(eq->hasLiteral()){
        equalities.push_back(eq);
      }
    }
  }

  vector<Constraint>::const_iterator i, j, eq_end = equalities.end();
  for(i = equalities.begin(); i != eq_end; ++i){
    Constraint at_i = *i;
    for(j= i + 1; j != eq_end; ++j){
      Constraint at_j = *j;

      mutuallyExclusive(out, at_i, at_j);
    }
  }

  for(i = equalities.begin(); i != eq_end; ++i){
    Constraint eq = *i;
    const ValueCollection& vc = eq->getValueCollection();
    Assert(vc.hasEquality() && vc.getEquality()->hasLiteral());

    bool hasLB = vc.hasLowerBound() && vc.getLowerBound()->hasLiteral();
    bool hasUB = vc.hasUpperBound() && vc.getUpperBound()->hasLiteral();

    Constraint lb = hasLB ?
      vc.getLowerBound() : eq->getStrictlyWeakerLowerBound(true, false);
    Constraint ub = hasUB ?
      vc.getUpperBound() : eq->getStrictlyWeakerUpperBound(true, false);

    if(hasUB && hasLB && !eq->isSplit()){
      out.push_back(eq->split());
    }
    if(lb != NullConstraint){
      implies(out, eq, lb);
    }
    if(ub != NullConstraint){
      implies(out, eq, ub);
    }
  }
}

void ConstraintDatabase::outputUnateEqualityLemmas(std::vector<Node>& lemmas) const{
  for(ArithVar v = 0, N = d_varDatabases.size(); v < N; ++v){
    outputUnateEqualityLemmas(lemmas, v);
  }
}

void ConstraintDatabase::outputUnateInequalityLemmas(std::vector<Node>& lemmas) const{
  for(ArithVar v = 0, N = d_varDatabases.size(); v < N; ++v){
    outputUnateInequalityLemmas(lemmas, v);
  }
}

void ConstraintDatabase::raiseUnateConflict(Constraint ant, Constraint cons){
  Assert(ant->hasProof());
  Constraint negCons = cons->getNegation();
  Assert(negCons->hasProof());

  Debug("arith::unate::conf") << ant << "implies " << cons << endl;
  Debug("arith::unate::conf") << negCons << " is true." << endl;


  Node conf = ConstraintValue::explainConflict(ant, negCons);
  Debug("arith::unate::conf") << conf << std::endl;
  d_raiseConflict(conf);
}

void ConstraintDatabase::unatePropLowerBound(Constraint curr, Constraint prev){
  Debug("arith::unate") << "unatePropLowerBound " << curr << " " << prev << endl;
  Assert(curr != prev);
  Assert(curr != NullConstraint);
  bool hasPrev = ! (prev == NullConstraint);
  Assert(!hasPrev || curr->getValue() > prev->getValue());

  ++d_statistics.d_unatePropagateCalls;

  const SortedConstraintMap& scm = curr->constraintSet();
  const SortedConstraintMapConstIterator scm_begin = scm.begin();
  SortedConstraintMapConstIterator scm_i = curr->d_variablePosition;

  //Ignore the first ValueCollection
  // NOPE: (>= p c) then (= p c) NOPE
  // NOPE: (>= p c) then (not (= p c)) NOPE

  while(scm_i != scm_begin){
    --scm_i; // move the iterator back

    const ValueCollection& vc = scm_i->second;

    //If it has the previous element, do nothing and stop!
    if(hasPrev &&
       vc.hasConstraintOfType(prev->getType())
       && vc.getConstraintOfType(prev->getType()) == prev){
      break;
    }

    //Don't worry about implying the negation of upperbound.
    //These should all be handled by propagating the LowerBounds!
    if(vc.hasLowerBound()){
      Constraint lb = vc.getLowerBound();
      if(lb->negationHasProof()){
        raiseUnateConflict(curr, lb);
        return;
      }else if(!lb->isTrue()){
        ++d_statistics.d_unatePropagateImplications;
        Debug("arith::unate") << "unatePropLowerBound " << curr << " implies " << lb << endl;

        lb->impliedBy(curr);
      }
    }
    if(vc.hasDisequality()){
      Constraint dis = vc.getDisequality();
      if(dis->negationHasProof()){
        raiseUnateConflict(curr, dis);
        return;
      }else if(!dis->isTrue()){
        ++d_statistics.d_unatePropagateImplications;
        Debug("arith::unate") << "unatePropLowerBound " << curr << " implies " << dis << endl;

        dis->impliedBy(curr);
      }
    }
  }
}

void ConstraintDatabase::unatePropUpperBound(Constraint curr, Constraint prev){
  Debug("arith::unate") << "unatePropUpperBound " << curr << " " << prev << endl;
  Assert(curr != prev);
  Assert(curr != NullConstraint);
  bool hasPrev = ! (prev == NullConstraint);
  Assert(!hasPrev || curr->getValue() < prev->getValue());

  ++d_statistics.d_unatePropagateCalls;

  const SortedConstraintMap& scm = curr->constraintSet();
  const SortedConstraintMapConstIterator scm_end = scm.end();
  SortedConstraintMapConstIterator scm_i = curr->d_variablePosition;
  ++scm_i;
  for(; scm_i != scm_end; ++scm_i){
    const ValueCollection& vc = scm_i->second;

    //If it has the previous element, do nothing and stop!
    if(hasPrev &&
       vc.hasConstraintOfType(prev->getType()) &&
       vc.getConstraintOfType(prev->getType()) == prev){
      break;
    }
    //Don't worry about implying the negation of upperbound.
    //These should all be handled by propagating the UpperBounds!
    if(vc.hasUpperBound()){
      Constraint ub = vc.getUpperBound();
      if(ub->negationHasProof()){
        raiseUnateConflict(curr, ub);
        return;
      }else if(!ub->isTrue()){
        ++d_statistics.d_unatePropagateImplications;
        Debug("arith::unate") << "unatePropUpperBound " << curr << " implies " << ub << endl;
        ub->impliedBy(curr);
      }
    }
    if(vc.hasDisequality()){
      Constraint dis = vc.getDisequality();
      if(dis->negationHasProof()){
        raiseUnateConflict(curr, dis);
        return;
      }else if(!dis->isTrue()){
        Debug("arith::unate") << "unatePropUpperBound " << curr << " implies " << dis << endl;
        ++d_statistics.d_unatePropagateImplications;

        dis->impliedBy(curr);
      }
    }
  }
}

void ConstraintDatabase::unatePropEquality(Constraint curr, Constraint prevLB, Constraint prevUB){
  Debug("arith::unate") << "unatePropEquality " << curr << " " << prevLB << " " << prevUB << endl;
  Assert(curr != prevLB);
  Assert(curr != prevUB);
  Assert(curr != NullConstraint);
  bool hasPrevLB = ! (prevLB == NullConstraint);
  bool hasPrevUB = ! (prevUB == NullConstraint);
  Assert(!hasPrevLB || curr->getValue() >= prevLB->getValue());
  Assert(!hasPrevUB || curr->getValue() <= prevUB->getValue());

  ++d_statistics.d_unatePropagateCalls;

  const SortedConstraintMap& scm = curr->constraintSet();
  SortedConstraintMapConstIterator scm_curr = curr->d_variablePosition;
  SortedConstraintMapConstIterator scm_last = hasPrevUB ? prevUB->d_variablePosition : scm.end();
  SortedConstraintMapConstIterator scm_i;
  if(hasPrevLB){
    scm_i = prevLB->d_variablePosition;
    if(scm_i != scm_curr){ // If this does not move this past scm_curr, move it one forward
      ++scm_i;
    }
  }else{
    scm_i = scm.begin();
  }

  for(; scm_i != scm_curr; ++scm_i){
    // between the previous LB and the curr
    const ValueCollection& vc = scm_i->second;

    //Don't worry about implying the negation of upperbound.
    //These should all be handled by propagating the LowerBounds!
    if(vc.hasLowerBound()){
      Constraint lb = vc.getLowerBound();
      if(lb->negationHasProof()){
        raiseUnateConflict(curr, lb);
        return;
      }else if(!lb->isTrue()){
        ++d_statistics.d_unatePropagateImplications;
        Debug("arith::unate") << "unatePropUpperBound " << curr << " implies " << lb << endl;
        lb->impliedBy(curr);
      }
    }
    if(vc.hasDisequality()){
      Constraint dis = vc.getDisequality();
      if(dis->negationHasProof()){
        raiseUnateConflict(curr, dis);
        return;
      }else if(!dis->isTrue()){
        ++d_statistics.d_unatePropagateImplications;
        Debug("arith::unate") << "unatePropUpperBound " << curr << " implies " << dis << endl;

        dis->impliedBy(curr);
      }
    }
  }
  Assert(scm_i == scm_curr);
  if(!hasPrevUB || scm_i != scm_last){
    ++scm_i;
  } // hasPrevUB implies scm_i != scm_last

  for(; scm_i != scm_last; ++scm_i){
    // between the curr and the previous UB imply the upperbounds and disequalities.
    const ValueCollection& vc = scm_i->second;

    //Don't worry about implying the negation of upperbound.
    //These should all be handled by propagating the UpperBounds!
    if(vc.hasUpperBound()){
      Constraint ub = vc.getUpperBound();
      if(ub->negationHasProof()){
        raiseUnateConflict(curr, ub);
        return;
      }else if(!ub->isTrue()){
        ++d_statistics.d_unatePropagateImplications;
        Debug("arith::unate") << "unateProp " << curr << " implies " << ub << endl;

        ub->impliedBy(curr);
      }
    }
    if(vc.hasDisequality()){
      Constraint dis = vc.getDisequality();
      if(dis->negationHasProof()){
        raiseUnateConflict(curr, dis);
        return;
      }else if(!dis->isTrue()){
        ++d_statistics.d_unatePropagateImplications;
        Debug("arith::unate") << "unateProp " << curr << " implies " << dis << endl;
        dis->impliedBy(curr);
      }
    }
  }
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
