/*********************                                                        */
/*! \file constraint.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Alex Ozdemir, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/
#include "theory/arith/constraint.h"

#include <algorithm>
#include <ostream>
#include <unordered_set>

#include "base/output.h"
#include "proof/proof.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/normal_form.h"


using namespace std;
using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace arith {

/** Given a simplifiedKind this returns the corresponding ConstraintType. */
//ConstraintType constraintTypeOfLiteral(Kind k);
ConstraintType Constraint::constraintTypeOfComparison(const Comparison& cmp){
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
  default: Unhandled() << k;
  }
}

Constraint::Constraint(ArithVar x,  ConstraintType t, const DeltaRational& v)
  : d_variable(x),
    d_type(t),
    d_value(v),
    d_database(NULL),
    d_literal(Node::null()),
    d_negation(NullConstraint),
    d_canBePropagated(false),
    d_assertionOrder(AssertionOrderSentinel),
    d_witness(TNode::null()),
    d_crid(ConstraintRuleIdSentinel),
    d_split(false),
    d_variablePosition()
{
  Assert(!initialized());
}


std::ostream& operator<<(std::ostream& o, const ArithProofType apt){
  switch(apt){
  case NoAP:  o << "NoAP"; break;
  case AssumeAP:  o << "AssumeAP"; break;
  case InternalAssumeAP:  o << "InternalAssumeAP"; break;
  case FarkasAP:  o << "FarkasAP"; break;
  case TrichotomyAP:  o << "TrichotomyAP"; break;
  case EqualityEngineAP:  o << "EqualityEngineAP"; break;
  case IntTightenAP: o << "IntTightenAP"; break;
  case IntHoleAP: o << "IntHoleAP"; break;
  default: break;
  }
  return o;
}

std::ostream& operator<<(std::ostream& o, const ConstraintCP c){
  if(c == NullConstraint){
    return o << "NullConstraint";
  }else{
    return o << *c;
  }
}

std::ostream& operator<<(std::ostream& o, const ConstraintP c){
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

std::ostream& operator<<(std::ostream& o, const Constraint& c){
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

std::ostream& operator<<(std::ostream& o, const ConstraintCPVec& v){
  o << "[" << v.size() << "x";
  ConstraintCPVec::const_iterator i, end;
  for(i=v.begin(), end=v.end(); i != end; ++i){
    ConstraintCP c = *i;
    o << ", " << (*c);
  }
  o << "]";
  return o;
}

void Constraint::debugPrint() const {
  Message() << *this << endl;
}


ValueCollection::ValueCollection()
  : d_lowerBound(NullConstraint),
    d_upperBound(NullConstraint),
    d_equality(NullConstraint),
    d_disequality(NullConstraint)
{}

bool ValueCollection::hasLowerBound() const{
  return d_lowerBound != NullConstraint;
}

bool ValueCollection::hasUpperBound() const{
  return d_upperBound != NullConstraint;
}

bool ValueCollection::hasEquality() const{
  return d_equality != NullConstraint;
}

bool ValueCollection::hasDisequality() const {
  return d_disequality != NullConstraint;
}

ConstraintP ValueCollection::getLowerBound() const {
  Assert(hasLowerBound());
  return d_lowerBound;
}

ConstraintP ValueCollection::getUpperBound() const {
  Assert(hasUpperBound());
  return d_upperBound;
}

ConstraintP ValueCollection::getEquality() const {
  Assert(hasEquality());
  return d_equality;
}

ConstraintP ValueCollection::getDisequality() const {
  Assert(hasDisequality());
  return d_disequality;
}


void ValueCollection::push_into(std::vector<ConstraintP>& vec) const {
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

ValueCollection ValueCollection::mkFromConstraint(ConstraintP c){
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

void ValueCollection::add(ConstraintP c){
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

ConstraintP ValueCollection::getConstraintOfType(ConstraintType t) const{
  switch(t){
    case LowerBound: Assert(hasLowerBound()); return d_lowerBound;
    case Equality: Assert(hasEquality()); return d_equality;
    case UpperBound: Assert(hasUpperBound()); return d_upperBound;
    case Disequality: Assert(hasDisequality()); return d_disequality;
    default: Unreachable();
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

ConstraintP ValueCollection::nonNull() const{
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

bool Constraint::initialized() const {
  return d_database != NULL;
}

const ConstraintDatabase& Constraint::getDatabase() const{
  Assert(initialized());
  return *d_database;
}

void Constraint::initialize(ConstraintDatabase* db, SortedConstraintMapIterator v, ConstraintP negation){
  Assert(!initialized());
  d_database = db;
  d_variablePosition = v;
  d_negation = negation;
}

Constraint::~Constraint() {
  // Call this instead of safeToGarbageCollect()
  Assert(!contextDependentDataIsSet());

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

const ConstraintRule& Constraint::getConstraintRule() const {
  Assert(hasProof());
  return d_database->d_watches->d_constraintProofs[d_crid];
}

const ValueCollection& Constraint::getValueCollection() const{
  return d_variablePosition->second;
}


ConstraintP Constraint::getCeiling() {
  Debug("getCeiling") << "Constraint_::getCeiling on " << *this << endl;
  Assert(getValue().getInfinitesimalPart().sgn() > 0);

  const DeltaRational ceiling(getValue().ceiling());
  return d_database->getConstraint(getVariable(), getType(), ceiling);
}

ConstraintP Constraint::getFloor() {
  Assert(getValue().getInfinitesimalPart().sgn() < 0);

  const DeltaRational floor(Rational(getValue().floor()));
  return d_database->getConstraint(getVariable(), getType(), floor);
}

void Constraint::setCanBePropagated() {
  Assert(!canBePropagated());
  d_database->pushCanBePropagatedWatch(this);
}

void Constraint::setAssertedToTheTheory(TNode witness, bool nowInConflict) {
  Assert(hasLiteral());
  Assert(!assertedToTheTheory());
  Assert(negationHasProof() == nowInConflict);
  d_database->pushAssertionOrderWatch(this, witness);

  if(Debug.isOn("constraint::conflictCommit") && nowInConflict ){
    Debug("constraint::conflictCommit") << "inConflict@setAssertedToTheTheory";
    Debug("constraint::conflictCommit") << "\t" << this << std::endl;
    Debug("constraint::conflictCommit") << "\t" << getNegation() << std::endl;
    Debug("constraint::conflictCommit") << "\t" << getNegation()->externalExplainByAssertions() << std::endl;

  }
}

bool Constraint::satisfiedBy(const DeltaRational& dr) const {
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

bool Constraint::isInternalAssumption() const {
  return getProofType() == InternalAssumeAP;
}

bool Constraint::isAssumption() const {
  return getProofType() == AssumeAP;
}

bool Constraint::hasEqualityEngineProof() const {
  return getProofType() == EqualityEngineAP;
}

bool Constraint::hasFarkasProof() const {
  return getProofType() == FarkasAP;
}

bool Constraint::hasSimpleFarkasProof() const
{
  Debug("constraints::hsfp") << "hasSimpleFarkasProof " << this << std::endl;
  if (!hasFarkasProof())
  {
    Debug("constraints::hsfp") << "There is no simple Farkas proof because "
                                  "there is no farkas proof."
                               << std::endl;
    return false;
  }

  // For each antecdent ...
  AntecedentId i = getConstraintRule().d_antecedentEnd;
  for (ConstraintCP a = d_database->getAntecedent(i); a != NullConstraint;
       a = d_database->getAntecedent(--i))
  {
    // ... that antecdent must be an assumption ...
    if (a->isAssumption())
    {
      continue;
    }

    // ... OR a tightened assumption ...
    if (a->hasIntTightenProof()
        && a->getConstraintRule().d_antecedentEnd != AntecedentIdSentinel
        && d_database->getAntecedent(a->getConstraintRule().d_antecedentEnd)
               ->isAssumption())

    {
      continue;
    }

    // ... otherwise, we do not have a simple Farkas proof.
    if (Debug.isOn("constraints::hsfp"))
    {
      Debug("constraints::hsfp") << "There is no simple Farkas proof b/c there "
                                    "is an antecdent w/ rule ";
      a->getConstraintRule().print(Debug("constraints::hsfp"));
      Debug("constraints::hsfp") << std::endl;
    }

    return false;
  }
  return true;
}

bool Constraint::hasIntTightenProof() const {
  return getProofType() == IntTightenAP;
}

bool Constraint::hasIntHoleProof() const {
  return getProofType() == IntHoleAP;
}

bool Constraint::hasTrichotomyProof() const {
  return getProofType() == TrichotomyAP;
}

void Constraint::printProofTree(std::ostream& out, size_t depth) const
{
#if IS_PROOFS_BUILD
  const ConstraintRule& rule = getConstraintRule();
  out << std::string(2 * depth, ' ') << "* " << getVariable() << " [";
  if (hasLiteral())
  {
    out << getLiteral();
  }
  else
  {
    out << "NOLIT";
  };
  out << "]" << ' ' << getType() << ' ' << getValue() << " (" << getProofType()
      << ")";
  if (getProofType() == FarkasAP)
  {
    out << " [";
    bool first = true;
    for (const auto& coeff : *rule.d_farkasCoefficients)
    {
      if (not first)
      {
        out << ", ";
      }
      first = false;
      out << coeff;
    }
    out << "]";
  }
  out << endl;

  for (AntecedentId i = rule.d_antecedentEnd; i != AntecedentIdSentinel; --i) {
    ConstraintCP antecdent = d_database->getAntecedent(i);
    if (antecdent == NullConstraint) {
      break;
    }
    antecdent->printProofTree(out, depth + 1);
  }
#else  /* IS_PROOFS_BUILD */
  out << "Cannot print proof. This is not a proof build." << endl;
#endif /* IS_PROOFS_BUILD */
}

bool Constraint::sanityChecking(Node n) const {
  Comparison cmp = Comparison::parseNormalForm(n);
  Kind k = cmp.comparisonKind();
  Polynomial pleft = cmp.normalizedVariablePart();
  Assert(k == EQUAL || k == DISTINCT || pleft.leadingCoefficientIsPositive());
  Assert(k != EQUAL || Monomial::isMember(n[0]));
  Assert(k != DISTINCT || Monomial::isMember(n[0][0]));

  TNode left = pleft.getNode();
  DeltaRational right = cmp.normalizedDeltaRational();

  const ArithVariables& avariables = d_database->getArithVariables();

  Debug("Constraint::sanityChecking") << cmp.getNode() << endl;
  Debug("Constraint::sanityChecking") << k << endl;
  Debug("Constraint::sanityChecking") << pleft.getNode() << endl;
  Debug("Constraint::sanityChecking") << left << endl;
  Debug("Constraint::sanityChecking") << right << endl;
  Debug("Constraint::sanityChecking") << getValue() << endl;
  Debug("Constraint::sanityChecking") << avariables.hasArithVar(left) << endl;
  Debug("Constraint::sanityChecking") << avariables.asArithVar(left) << endl;
  Debug("Constraint::sanityChecking") << getVariable() << endl;


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

void ConstraintRule::debugPrint() const {
  print(std::cerr);
}

ConstraintCP ConstraintDatabase::getAntecedent (AntecedentId p) const {
  Assert(p < d_antecedents.size());
  return d_antecedents[p];
}


void ConstraintRule::print(std::ostream& out) const {
  
  RationalVectorCP coeffs = NULLPROOF(d_farkasCoefficients);
  out << "{ConstraintRule, ";
  out << d_constraint << std::endl;
  out << "d_proofType= " << d_proofType << ", " << std::endl;
  out << "d_antecedentEnd= "<< d_antecedentEnd << std::endl;

  if (d_constraint != NullConstraint && d_antecedentEnd != AntecedentIdSentinel)
  {
    const ConstraintDatabase& database = d_constraint->getDatabase();
    
    size_t coeffIterator = (coeffs != RationalVectorCPSentinel) ? coeffs->size()-1 : 0;
    AntecedentId p = d_antecedentEnd;
    // must have at least one antecedent
    ConstraintCP antecedent = database.getAntecedent(p);
    while(antecedent != NullConstraint){
      if(coeffs != RationalVectorCPSentinel){
        out << coeffs->at(coeffIterator);
      } else {
        out << "_";
      }
      out << " * (" << *antecedent << ")" << std::endl;

      Assert((coeffs == RationalVectorCPSentinel) || coeffIterator > 0);
      --p;
      coeffIterator = (coeffs != RationalVectorCPSentinel) ? coeffIterator-1 : 0;
      antecedent = database.getAntecedent(p);
    }
    if(coeffs != RationalVectorCPSentinel){
      out << coeffs->front();
    } else {
      out << "_";
    }
    out << " * (" << *(d_constraint->getNegation()) << ")";
    out << " [not d_constraint] " << endl;
  }
  out << "}";
}

bool Constraint::wellFormedFarkasProof() const {
  Assert(hasProof());

  const ConstraintRule& cr = getConstraintRule();
  if(cr.d_constraint != this){ return false; }
  if(cr.d_proofType != FarkasAP){ return false; }

  AntecedentId p = cr.d_antecedentEnd;

  // must have at least one antecedent
  ConstraintCP antecedent = d_database->d_antecedents[p];
  if(antecedent  == NullConstraint) { return false; }

#if IS_PROOFS_BUILD
  if(!PROOF_ON()){ return cr.d_farkasCoefficients == RationalVectorCPSentinel; }
  Assert(PROOF_ON());

  if(cr.d_farkasCoefficients == RationalVectorCPSentinel){ return false; }
  if(cr.d_farkasCoefficients->size() < 2){ return false; }

  const ArithVariables& vars = d_database->getArithVariables();

  DeltaRational rhs(0);
  Node lhs = Polynomial::mkZero().getNode();

  RationalVector::const_iterator coeffIterator = cr.d_farkasCoefficients->end()-1;
  RationalVector::const_iterator coeffBegin = cr.d_farkasCoefficients->begin();

  while(antecedent != NullConstraint){
    Assert(lhs.isNull() || Polynomial::isMember(lhs));

    const Rational& coeff = *coeffIterator;
    int coeffSgn = coeff.sgn();

    rhs += antecedent->getValue() * coeff;

    ArithVar antVar = antecedent->getVariable();
    if(!lhs.isNull() && vars.hasNode(antVar)){
      Node antAsNode = vars.asNode(antVar);
      if(Polynomial::isMember(antAsNode)){
        Polynomial lhsPoly = Polynomial::parsePolynomial(lhs);
        Polynomial antPoly = Polynomial::parsePolynomial(antAsNode);
        Polynomial sum = lhsPoly + (antPoly * coeff);
        lhs = sum.getNode();
      }else{
        lhs = Node::null();
      }
    } else {
      lhs = Node::null();
    }
    Debug("constraints::wffp") << "running sum: " << lhs << " <= " << rhs << endl;

    switch( antecedent->getType() ){
    case LowerBound:
      // fc[l] < 0, therefore return false if coeffSgn >= 0
      if(coeffSgn >= 0){ return false; }
      break;
    case UpperBound:
      // fc[u] > 0, therefore return false if coeffSgn <= 0
      if(coeffSgn <= 0){ return false; }
      break;
    case Equality:
      if(coeffSgn == 0) { return false; }
      break;
    case Disequality:
    default:
      return false;
    }
    
    if(coeffIterator == coeffBegin){ return false; }
    --coeffIterator;
    --p;
    antecedent = d_database->d_antecedents[p];
  }
  if(coeffIterator != coeffBegin){ return false; }

  const Rational& firstCoeff = (*coeffBegin);
  int firstCoeffSgn = firstCoeff.sgn();
  rhs += (getNegation()->getValue()) * firstCoeff;
  if(!lhs.isNull() && vars.hasNode(getVariable())){
    Node firstAsNode = vars.asNode(getVariable());
    if(Polynomial::isMember(firstAsNode)){
      Polynomial lhsPoly = Polynomial::parsePolynomial(lhs);
      Polynomial firstPoly = Polynomial::parsePolynomial(firstAsNode);
      Polynomial sum = lhsPoly + (firstPoly * firstCoeff);
      lhs = sum.getNode();
    }else{
      lhs = Node::null();
    }
  }else{
    lhs = Node::null();
  }

  switch( getNegation()->getType() ){
  case LowerBound:
    // fc[l] < 0, therefore return false if coeffSgn >= 0
    if(firstCoeffSgn >= 0){ return false; }
    break;
  case UpperBound:
    // fc[u] > 0, therefore return false if coeffSgn <= 0
    if(firstCoeffSgn <= 0){ return false; }
    break;
  case Equality:
    if(firstCoeffSgn == 0) { return false; }
    break;
  case Disequality:
  default:
    return false;
  }
  Debug("constraints::wffp") << "final sum: " << lhs << " <= " << rhs << endl;
  // 0 = lhs <= rhs < 0
  return (lhs.isNull() || (Constant::isMember(lhs) && Constant(lhs).isZero()))
         && rhs.sgn() < 0;

#else  /* IS_PROOFS_BUILD */
  return true;
#endif /* IS_PROOFS_BUILD */
}

ConstraintP Constraint::makeNegation(ArithVar v, ConstraintType t, const DeltaRational& r){
  switch(t){
  case LowerBound:
    {
      Assert(r.infinitesimalSgn() >= 0);
      if(r.infinitesimalSgn() > 0){
        Assert(r.getInfinitesimalPart() == 1);
        // make (not (v > r)), which is (v <= r)
        DeltaRational dropInf(r.getNoninfinitesimalPart(), 0);
        return new Constraint(v, UpperBound, dropInf);
      }else{
        Assert(r.infinitesimalSgn() == 0);
        // make (not (v >= r)), which is (v < r)
        DeltaRational addInf(r.getNoninfinitesimalPart(), -1);
        return new Constraint(v, UpperBound, addInf);
      }
    }
  case UpperBound:
    {
      Assert(r.infinitesimalSgn() <= 0);
      if(r.infinitesimalSgn() < 0){
        Assert(r.getInfinitesimalPart() == -1);
        // make (not (v < r)), which is (v >= r)
        DeltaRational dropInf(r.getNoninfinitesimalPart(), 0);
        return new Constraint(v, LowerBound, dropInf);
      }else{
        Assert(r.infinitesimalSgn() == 0);
        // make (not (v <= r)), which is (v > r)
        DeltaRational addInf(r.getNoninfinitesimalPart(), 1);
        return new Constraint(v, LowerBound, addInf);
      }
    }
  case Equality:
    return new Constraint(v, Disequality, r);
  case Disequality:
    return new Constraint(v, Equality, r);
  default:
    Unreachable();
    return NullConstraint;
  }
}

ConstraintDatabase::ConstraintDatabase(context::Context* satContext, context::Context* userContext, const ArithVariables& avars, ArithCongruenceManager& cm, RaiseConflict raiseConflict)
  : d_varDatabases()
  , d_toPropagate(satContext)
  , d_antecedents(satContext, false)
  , d_watches(new Watches(satContext, userContext))
  , d_avariables(avars)
  , d_congruenceManager(cm)
  , d_satContext(satContext)
  , d_raiseConflict(raiseConflict)
  , d_one(1)
  , d_negOne(-1)
{
  
}

SortedConstraintMap& ConstraintDatabase::getVariableSCM(ArithVar v) const{
  Assert(variableDatabaseIsSetup(v));
  return d_varDatabases[v]->d_constraints;
}

void ConstraintDatabase::pushSplitWatch(ConstraintP c){
  Assert(!c->d_split);
  c->d_split = true;
  d_watches->d_splitWatches.push_back(c);
}


void ConstraintDatabase::pushCanBePropagatedWatch(ConstraintP c){
  Assert(!c->d_canBePropagated);
  c->d_canBePropagated = true;
  d_watches->d_canBePropagatedWatches.push_back(c);
}

void ConstraintDatabase::pushAssertionOrderWatch(ConstraintP c, TNode witness){
  Assert(!c->assertedToTheTheory());
  c->d_assertionOrder = d_watches->d_assertionOrderWatches.size();
  c->d_witness = witness;
  d_watches->d_assertionOrderWatches.push_back(c);
}


void ConstraintDatabase::pushConstraintRule(const ConstraintRule& crp){
  ConstraintP c = crp.d_constraint;
  Assert(c->d_crid == ConstraintRuleIdSentinel);
  Assert(!c->hasProof());
  c->d_crid = d_watches->d_constraintProofs.size();
  d_watches->d_constraintProofs.push_back(crp);
}

ConstraintP ConstraintDatabase::getConstraint(ArithVar v, ConstraintType t, const DeltaRational& r){
  //This must always return a constraint.

  SortedConstraintMap& scm = getVariableSCM(v);
  pair<SortedConstraintMapIterator, bool> insertAttempt;
  insertAttempt = scm.insert(make_pair(r, ValueCollection()));

  SortedConstraintMapIterator pos = insertAttempt.first;
  ValueCollection& vc = pos->second;
  if(vc.hasConstraintOfType(t)){
    return vc.getConstraintOfType(t);
  }else{
    ConstraintP c = new Constraint(v, t, r);
    ConstraintP negC = Constraint::makeNegation(v, t, r);

    SortedConstraintMapIterator negPos;
    if(t == Equality || t == Disequality){
      negPos = pos;
    }else{
      pair<SortedConstraintMapIterator, bool> negInsertAttempt;
      negInsertAttempt = scm.insert(make_pair(negC->getValue(), ValueCollection()));
      Assert(negInsertAttempt.second
             || !negInsertAttempt.first->second.hasConstraintOfType(
                 negC->getType()));
      negPos = negInsertAttempt.first;
    }

    c->initialize(this, pos, negC);
    negC->initialize(this, negPos, c);

    vc.add(c);
    negPos->second.add(negC);

    return c;
  }
}

ConstraintP ConstraintDatabase::ensureConstraint(ValueCollection& vc, ConstraintType t){
  if(vc.hasConstraintOfType(t)){
    return vc.getConstraintOfType(t);
  }else{
    return getConstraint(vc.getVariable(), t, vc.getValue());
  }
}

bool ConstraintDatabase::emptyDatabase(const std::vector<PerVariableDatabase>& vec){
  std::vector<PerVariableDatabase>::const_iterator first = vec.begin();
  std::vector<PerVariableDatabase>::const_iterator last = vec.end();
  return std::find_if(first, last, PerVariableDatabase::IsEmpty) == last;
}

ConstraintDatabase::~ConstraintDatabase(){
  delete d_watches;

  std::vector<ConstraintP> constraintList;

  while(!d_varDatabases.empty()){
    PerVariableDatabase* back = d_varDatabases.back();

    SortedConstraintMap& scm = back->d_constraints;
    SortedConstraintMapIterator i = scm.begin(), i_end = scm.end();
    for(; i != i_end; ++i){
      (i->second).push_into(constraintList);
    }
    while(!constraintList.empty()){
      ConstraintP c = constraintList.back();
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
  smtStatisticsRegistry()->registerStat(&d_unatePropagateCalls);
  smtStatisticsRegistry()->registerStat(&d_unatePropagateImplications);

}

ConstraintDatabase::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_unatePropagateCalls);
  smtStatisticsRegistry()->unregisterStat(&d_unatePropagateImplications);
}

void ConstraintDatabase::deleteConstraintAndNegation(ConstraintP c){
  Assert(c->safeToGarbageCollect());
  ConstraintP neg = c->getNegation();
  Assert(neg->safeToGarbageCollect());
  delete c;
  delete neg;
}

void ConstraintDatabase::addVariable(ArithVar v){
  if(d_reclaimable.isMember(v)){
    SortedConstraintMap& scm = getVariableSCM(v);

    std::vector<ConstraintP> constraintList;

    for(SortedConstraintMapIterator i = scm.begin(), end = scm.end(); i != end; ++i){
      (i->second).push_into(constraintList);
    }
    while(!constraintList.empty()){
      ConstraintP c = constraintList.back();
      constraintList.pop_back();
      Assert(c->safeToGarbageCollect());
      delete c;
    }
    Assert(scm.empty());

    d_reclaimable.remove(v);
  }else{
    Debug("arith::constraint") << "about to fail" << v << " " << d_varDatabases.size() << endl;
    Assert(v == d_varDatabases.size());
    d_varDatabases.push_back(new PerVariableDatabase(v));
  }
}

void ConstraintDatabase::removeVariable(ArithVar v){
  Assert(!d_reclaimable.isMember(v));
  d_reclaimable.add(v);
}

bool Constraint::safeToGarbageCollect() const{
  // Do not call during destructor as getNegation() may be Null by this point
  Assert(getNegation() != NullConstraint);
  return !contextDependentDataIsSet() && ! getNegation()->contextDependentDataIsSet();
}

bool Constraint::contextDependentDataIsSet() const{
  return hasProof() || isSplit() || canBePropagated() || assertedToTheTheory();
}

Node Constraint::split(){
  Assert(isEquality() || isDisequality());

  bool isEq = isEquality();

  ConstraintP eq = isEq ? this : d_negation;
  ConstraintP diseq = isEq ? d_negation : this;

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

ConstraintP ConstraintDatabase::addLiteral(TNode literal){
  Assert(!hasLiteral(literal));
  bool isNot = (literal.getKind() == NOT);
  Node atomNode = (isNot ? literal[0] : literal);
  Node negationNode  = atomNode.notNode();

  Assert(!hasLiteral(atomNode));
  Assert(!hasLiteral(negationNode));
  Comparison posCmp = Comparison::parseNormalForm(atomNode);

  ConstraintType posType = Constraint::constraintTypeOfComparison(posCmp);

  Polynomial nvp = posCmp.normalizedVariablePart();
  ArithVar v = d_avariables.asArithVar(nvp.getNode());

  DeltaRational posDR = posCmp.normalizedDeltaRational();

  ConstraintP posC = new Constraint(v, posType, posDR);

  Debug("arith::constraint") << "addliteral( literal ->" << literal << ")" << endl;
  Debug("arith::constraint") << "addliteral( posC ->" << posC << ")" << endl;

  SortedConstraintMap& scm = getVariableSCM(posC->getVariable());
  pair<SortedConstraintMapIterator, bool> insertAttempt;
  insertAttempt = scm.insert(make_pair(posC->getValue(), ValueCollection()));

  SortedConstraintMapIterator posI = insertAttempt.first;
  // If the attempt succeeds, i points to a new empty ValueCollection
  // If the attempt fails, i points to a pre-existing ValueCollection

  if(posI->second.hasConstraintOfType(posC->getType())){
    //This is the situation where the ConstraintP exists, but
    //the literal has not been  associated with it.
    ConstraintP hit = posI->second.getConstraintOfType(posC->getType());
    Debug("arith::constraint") << "hit " << hit << endl;
    Debug("arith::constraint") << "posC " << posC << endl;

    delete posC;

    hit->setLiteral(atomNode);
    hit->getNegation()->setLiteral(negationNode);
    return isNot ? hit->getNegation(): hit;
  }else{
    Comparison negCmp = Comparison::parseNormalForm(negationNode);
    
    ConstraintType negType = Constraint::constraintTypeOfComparison(negCmp);
    DeltaRational negDR = negCmp.normalizedDeltaRational();

    ConstraintP negC = new Constraint(v, negType, negDR);

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


ConstraintP ConstraintDatabase::lookup(TNode literal) const{
  NodetoConstraintMap::const_iterator iter = d_nodetoConstraintMap.find(literal);
  if(iter == d_nodetoConstraintMap.end()){
    return NullConstraint;
  }else{
    return iter->second;
  }
}

void Constraint::setAssumption(bool nowInConflict){
  Debug("constraints::pf") << "setAssumption(" << this << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(hasLiteral());
  Assert(assertedToTheTheory());

  d_database->pushConstraintRule(ConstraintRule(this, AssumeAP));

  Assert(inConflict() == nowInConflict);
  if(Debug.isOn("constraint::conflictCommit") && inConflict()){
    Debug("constraint::conflictCommit") << "inConflict@setAssumption " << this << std::endl;
  }
}

void Constraint::tryToPropagate(){
  Assert(hasProof());
  Assert(!isAssumption());
  Assert(!isInternalAssumption());

  if(canBePropagated() && !assertedToTheTheory() && !isAssumption() && !isInternalAssumption()){
    propagate();
  }
}

void Constraint::propagate(){
  Assert(hasProof());
  Assert(canBePropagated());
  Assert(!assertedToTheTheory());
  Assert(!isAssumption());
  Assert(!isInternalAssumption());

  d_database->d_toPropagate.push(this);
}


/*
 * Example:
 *    x <= a and a < b
 * |= x <= b
 * ---
 *  1*(x <= a) + (-1)*(x > b) => (0 <= a-b)
 */
void Constraint::impliedByUnate(ConstraintCP imp, bool nowInConflict){
  Debug("constraints::pf") << "impliedByUnate(" << this << ", " << *imp << ")" << std::endl;
  Assert(!hasProof());
  Assert(imp->hasProof());
  Assert(negationHasProof() == nowInConflict);

  d_database->d_antecedents.push_back(NullConstraint);
  d_database->d_antecedents.push_back(imp);

  AntecedentId antecedentEnd = d_database->d_antecedents.size() - 1;

  RationalVectorP coeffs;
  if(PROOF_ON()){
    std::pair<int, int> sgns = unateFarkasSigns(getNegation(), imp);

    Rational first(sgns.first);
    Rational second(sgns.second);

    coeffs = new RationalVector();
    coeffs->push_back(first);
    coeffs->push_back(second);
  } else {
    coeffs = RationalVectorPSentinel;
  }

  // no need to delete coeffs the memory is owned by ConstraintRule
  d_database->pushConstraintRule(ConstraintRule(this, FarkasAP, antecedentEnd, coeffs));

  Assert(inConflict() == nowInConflict);
  if(Debug.isOn("constraint::conflictCommit") && inConflict()){
    Debug("constraint::conflictCommit") << "inConflict@impliedByUnate " << this << std::endl;
  }
  
  if(Debug.isOn("constraints::wffp") && !wellFormedFarkasProof()){
    getConstraintRule().print(Debug("constraints::wffp"));
  }
  Assert(wellFormedFarkasProof());
}

void Constraint::impliedByTrichotomy(ConstraintCP a, ConstraintCP b, bool nowInConflict){
  Debug("constraints::pf") << "impliedByTrichotomy(" << this << ", " << *a << ", ";
  Debug("constraints::pf") << *b << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(a->hasProof());
  Assert(b->hasProof());

  d_database->d_antecedents.push_back(NullConstraint);
  d_database->d_antecedents.push_back(a);
  d_database->d_antecedents.push_back(b);

  AntecedentId antecedentEnd = d_database->d_antecedents.size() - 1;
  d_database->pushConstraintRule(ConstraintRule(this, TrichotomyAP, antecedentEnd));

  Assert(inConflict() == nowInConflict);
  if(Debug.isOn("constraint::conflictCommit") && inConflict()){
    Debug("constraint::conflictCommit") << "inConflict@impliedByTrichotomy " << this << std::endl;
  }
}


bool Constraint::allHaveProof(const ConstraintCPVec& b){
  for(ConstraintCPVec::const_iterator i=b.begin(), i_end=b.end(); i != i_end; ++i){
    ConstraintCP cp = *i;
    if(! (cp->hasProof())){ return false; }
  }
  return true;
}

void Constraint::impliedByIntTighten(ConstraintCP a, bool nowInConflict){
  Debug("constraints::pf") << "impliedByIntTighten(" << this << ", " << *a << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(a->hasProof());
  Debug("pf::arith") << "impliedByIntTighten(" << this << ", " << a << ")"
                     << std::endl;

  d_database->d_antecedents.push_back(NullConstraint);
  d_database->d_antecedents.push_back(a);
  AntecedentId antecedentEnd = d_database->d_antecedents.size() - 1;
  d_database->pushConstraintRule(ConstraintRule(this, IntTightenAP, antecedentEnd));

  Assert(inConflict() == nowInConflict);
  if(inConflict()){
    Debug("constraint::conflictCommit") << "inConflict impliedByIntTighten" << this << std::endl;
  }
}

void Constraint::impliedByIntHole(ConstraintCP a, bool nowInConflict){
  Debug("constraints::pf") << "impliedByIntHole(" << this << ", " << *a << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(a->hasProof());
  Debug("pf::arith") << "impliedByIntHole(" << this << ", " << a << ")"
                     << std::endl;

  d_database->d_antecedents.push_back(NullConstraint);
  d_database->d_antecedents.push_back(a);
  AntecedentId antecedentEnd = d_database->d_antecedents.size() - 1;
  d_database->pushConstraintRule(ConstraintRule(this, IntHoleAP, antecedentEnd));

  Assert(inConflict() == nowInConflict);
  if(Debug.isOn("constraint::conflictCommit") && inConflict()){
    Debug("constraint::conflictCommit") << "inConflict impliedByIntHole" << this << std::endl;
  }
}

void Constraint::impliedByIntHole(const ConstraintCPVec& b, bool nowInConflict){
  Debug("constraints::pf") << "impliedByIntHole(" << this;
  if (Debug.isOn("constraints::pf")) {
    for (const ConstraintCP& p : b)
    {
      Debug("constraints::pf") << ", " << p;
    }
  }
  Debug("constraints::pf") << ")" << std::endl;

  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(allHaveProof(b));

  CDConstraintList& antecedents = d_database->d_antecedents;
  antecedents.push_back(NullConstraint);
  for(ConstraintCPVec::const_iterator i=b.begin(), i_end=b.end(); i != i_end; ++i){
    antecedents.push_back(*i);
  }
  AntecedentId antecedentEnd = antecedents.size() - 1;

  d_database->pushConstraintRule(ConstraintRule(this, IntHoleAP, antecedentEnd));

  Assert(inConflict() == nowInConflict);
  if(Debug.isOn("constraint::conflictCommit") && inConflict()){
    Debug("constraint::conflictCommit") << "inConflict@impliedByIntHole[vec] " << this << std::endl;
  }
}

/*
 * If proofs are off, coeffs == RationalVectorSentinal.
 * If proofs are on,
 *   coeffs != RationalVectorSentinal,
 *   coeffs->size() = a.size() + 1,
 *   for i in [0,a.size) : coeff[i] corresponds to a[i], and
 *   coeff.back() corresponds to the current constraint. 
 */
void Constraint::impliedByFarkas(const ConstraintCPVec& a, RationalVectorCP coeffs, bool nowInConflict){
  Debug("constraints::pf") << "impliedByFarkas(" << this;
  if (Debug.isOn("constraints::pf")) {
    for (const ConstraintCP& p : a)
    {
      Debug("constraints::pf") << ", " << p;
    }
  }
  Debug("constraints::pf") << ", <coeffs>";
  Debug("constraints::pf") << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(allHaveProof(a));

  Assert(PROOF_ON() == (coeffs != RationalVectorCPSentinel));
  // !PROOF_ON() => coeffs == RationalVectorCPSentinel
  //  PROOF_ON() => coeffs->size() == a.size() + 1
  Assert(!PROOF_ON() || coeffs->size() == a.size() + 1);
  Assert(a.size() >= 1);

  d_database->d_antecedents.push_back(NullConstraint);
  for(ConstraintCPVec::const_iterator i = a.begin(), end = a.end(); i != end; ++i){
    ConstraintCP c_i = *i;
    Assert(c_i->hasProof());
    d_database->d_antecedents.push_back(c_i);
  }
  AntecedentId antecedentEnd = d_database->d_antecedents.size() - 1;

  RationalVectorCP coeffsCopy;
  if(PROOF_ON()){
    Assert(coeffs != RationalVectorCPSentinel);
    coeffsCopy = new RationalVector(*coeffs);
  } else {
    coeffsCopy = RationalVectorCPSentinel;
  }
  d_database->pushConstraintRule(ConstraintRule(this, FarkasAP, antecedentEnd, coeffsCopy));

  Assert(inConflict() == nowInConflict);
  if(Debug.isOn("constraint::conflictCommit") && inConflict()){
    Debug("constraint::conflictCommit") << "inConflict@impliedByFarkas " << this << std::endl;
  }
  if(Debug.isOn("constraints::wffp") && !wellFormedFarkasProof()){
    getConstraintRule().print(Debug("constraints::wffp"));
  }
  Assert(wellFormedFarkasProof());
}


void Constraint::setInternalAssumption(bool nowInConflict){
  Debug("constraints::pf") << "setInternalAssumption(" << this;
  Debug("constraints::pf") << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(!assertedToTheTheory());

  d_database->pushConstraintRule(ConstraintRule(this, InternalAssumeAP));

  Assert(inConflict() == nowInConflict);
  if(Debug.isOn("constraint::conflictCommit") && inConflict()){
    Debug("constraint::conflictCommit") << "inConflict@setInternalAssumption " << this << std::endl;
  }
}


void Constraint::setEqualityEngineProof(){
  Debug("constraints::pf") << "setEqualityEngineProof(" << this;
  Debug("constraints::pf") << ")" << std::endl;
  Assert(truthIsUnknown());
  Assert(hasLiteral());
  d_database->pushConstraintRule(ConstraintRule(this, EqualityEngineAP));
}


SortedConstraintMap& Constraint::constraintSet() const{
  Assert(d_database->variableDatabaseIsSetup(d_variable));
  return (d_database->d_varDatabases[d_variable])->d_constraints;
}

bool Constraint::antecentListIsEmpty() const{
  Assert(hasProof());
  return d_database->d_antecedents[getEndAntecedent()] == NullConstraint;
}

bool Constraint::antecedentListLengthIsOne() const {
  Assert(hasProof());
  return !antecentListIsEmpty() &&
    d_database->d_antecedents[getEndAntecedent()-1] == NullConstraint;
}

Node Constraint::externalImplication(const ConstraintCPVec& b) const{
  Assert(hasLiteral());
  Node antecedent = externalExplainByAssertions(b);
  Node implied = getLiteral();
  return antecedent.impNode(implied);
}


Node Constraint::externalExplainByAssertions(const ConstraintCPVec& b){
  return externalExplain(b, AssertionOrderSentinel);
}

Node Constraint::externalExplainConflict() const{
  Debug("pf::arith::explain") << this << std::endl;
  Assert(inConflict());
  NodeBuilder<> nb(kind::AND);
  externalExplainByAssertions(nb);
  getNegation()->externalExplainByAssertions(nb);

  return safeConstructNary(nb);
}

struct ConstraintCPHash {
  /* Todo replace with an id */
  size_t operator()(ConstraintCP c) const{
    Assert(sizeof(ConstraintCP) > 0);
    return ((size_t)c)/sizeof(ConstraintCP);
  }
};

void Constraint::assertionFringe(ConstraintCPVec& v){
  unordered_set<ConstraintCP, ConstraintCPHash> visited;
  size_t writePos = 0;

  if(!v.empty()){
    const ConstraintDatabase* db = v.back()->d_database;
    const CDConstraintList& antecedents = db->d_antecedents;
    for(size_t i = 0; i < v.size(); ++i){
      ConstraintCP vi = v[i];
      if(visited.find(vi) == visited.end()){
        Assert(vi->hasProof());
        visited.insert(vi);
        if(vi->onFringe()){
          v[writePos] = vi;
          writePos++;
        }else{
          Assert(vi->hasTrichotomyProof() || vi->hasFarkasProof()
                 || vi->hasIntHoleProof() || vi->hasIntTightenProof());
          AntecedentId p = vi->getEndAntecedent();

          ConstraintCP antecedent = antecedents[p];
          while(antecedent != NullConstraint){
            v.push_back(antecedent);
            --p;
            antecedent = antecedents[p];
          }
        }
      }
    }
    v.resize(writePos);
  }
}

void Constraint::assertionFringe(ConstraintCPVec& o, const ConstraintCPVec& i){
  o.insert(o.end(), i.begin(), i.end());
  assertionFringe(o);
}

Node Constraint::externalExplain(const ConstraintCPVec& v, AssertionOrder order){
  NodeBuilder<> nb(kind::AND);
  ConstraintCPVec::const_iterator i, end;
  for(i = v.begin(), end = v.end(); i != end; ++i){
    ConstraintCP v_i = *i;
    v_i->externalExplain(nb, order);
  }
  return safeConstructNary(nb);
}

void Constraint::externalExplain(NodeBuilder<>& nb, AssertionOrder order) const{
  Assert(hasProof());
  Assert(!isAssumption() || assertedToTheTheory());
  Assert(!isInternalAssumption());

  if (Debug.isOn("pf::arith::explain"))
  {
    Debug("pf::arith::explain") << "Explaining: " << this << " with rule ";
    getConstraintRule().print(Debug("pf::arith::explain"));
    Debug("pf::arith::explain") << std::endl;
  }

  if(assertedBefore(order)){
    nb << getWitness();
  }else if(hasEqualityEngineProof()){
    d_database->eeExplain(this, nb);
  }else{
    Assert(!isAssumption());
    AntecedentId p = getEndAntecedent();
    ConstraintCP antecedent = d_database->d_antecedents[p];

    while(antecedent != NullConstraint){
      Debug("pf::arith::explain") << "Explain " << antecedent << std::endl;
      antecedent->externalExplain(nb, order);
      --p;
      antecedent = d_database->d_antecedents[p];
    }
  }
}

Node Constraint::externalExplain(AssertionOrder order) const{
  Assert(hasProof());
  Assert(!isAssumption() || assertedBefore(order));
  Assert(!isInternalAssumption());
  if(assertedBefore(order)){
    return getWitness();
  }else if(hasEqualityEngineProof()){
    return d_database->eeExplain(this);
  }else{
    Assert(hasFarkasProof() || hasIntHoleProof() || hasIntTightenProof() || hasTrichotomyProof());
    Assert(!antecentListIsEmpty());
    //Force the selection of the layer above if the node is
    // assertedToTheTheory()!

    AntecedentId listEnd = getEndAntecedent();
    if(antecedentListLengthIsOne()){
      ConstraintCP antecedent = d_database->d_antecedents[listEnd];
      return antecedent->externalExplain(order);
    }else{
      NodeBuilder<> nb(kind::AND);
      Assert(!isAssumption());

      AntecedentId p = listEnd;
      ConstraintCP antecedent = d_database->d_antecedents[p];
      while(antecedent != NullConstraint){
        antecedent->externalExplain(nb, order);
        --p;
        antecedent = d_database->d_antecedents[p];
      }
      return nb;
    }
  }
}

Node Constraint::externalExplainByAssertions(ConstraintCP a, ConstraintCP b){
  NodeBuilder<> nb(kind::AND);
  a->externalExplainByAssertions(nb);
  b->externalExplainByAssertions(nb);
  return nb;
}

Node Constraint::externalExplainByAssertions(ConstraintCP a, ConstraintCP b, ConstraintCP c){
  NodeBuilder<> nb(kind::AND);
  a->externalExplainByAssertions(nb);
  b->externalExplainByAssertions(nb);
  c->externalExplainByAssertions(nb);
  return nb;
}

ConstraintP Constraint::getStrictlyWeakerLowerBound(bool hasLiteral, bool asserted) const {
  Assert(initialized());
  Assert(!asserted || hasLiteral);

  SortedConstraintMapConstIterator i = d_variablePosition;
  const SortedConstraintMap& scm = constraintSet();
  SortedConstraintMapConstIterator i_begin = scm.begin();
  while(i != i_begin){
    --i;
    const ValueCollection& vc = i->second;
    if(vc.hasLowerBound()){
      ConstraintP weaker = vc.getLowerBound();

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

ConstraintP Constraint::getStrictlyWeakerUpperBound(bool hasLiteral, bool asserted) const {
  SortedConstraintMapConstIterator i = d_variablePosition;
  const SortedConstraintMap& scm = constraintSet();
  SortedConstraintMapConstIterator i_end = scm.end();

  ++i;
  for(; i != i_end; ++i){
    const ValueCollection& vc = i->second;
    if(vc.hasUpperBound()){
      ConstraintP weaker = vc.getUpperBound();
      if((!hasLiteral || (weaker->hasLiteral())) &&
         (!asserted || ( weaker->assertedToTheTheory()))){
        return weaker;
      }
    }
  }

  return NullConstraint;
}

ConstraintP ConstraintDatabase::getBestImpliedBound(ArithVar v, ConstraintType t, const DeltaRational& r) const {
  Assert(variableDatabaseIsSetup(v));
  Assert(t == UpperBound || t == LowerBound);

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
Node ConstraintDatabase::eeExplain(const Constraint* const c) const{
  Assert(c->hasLiteral());
  return d_congruenceManager.explain(c->getLiteral());
}

void ConstraintDatabase::eeExplain(const Constraint* const c, NodeBuilder<>& nb) const{
  Assert(c->hasLiteral());
  d_congruenceManager.explain(c->getLiteral(), nb);
}

bool ConstraintDatabase::variableDatabaseIsSetup(ArithVar v) const {
  return v < d_varDatabases.size();
}


ConstraintDatabase::Watches::Watches(context::Context* satContext, context::Context* userContext):
  d_constraintProofs(satContext),
  d_canBePropagatedWatches(satContext),
  d_assertionOrderWatches(satContext),
  d_splitWatches(userContext)
{}


void Constraint::setLiteral(Node n) {
  Assert(!hasLiteral());
  Assert(sanityChecking(n));
  d_literal = n;
  NodetoConstraintMap& map = d_database->d_nodetoConstraintMap;
  Assert(map.find(n) == map.end());
  map.insert(make_pair(d_literal, this));
}

void implies(std::vector<Node>& out, ConstraintP a, ConstraintP b){
  Node la = a->getLiteral();
  Node lb = b->getLiteral();

  Node neg_la = (la.getKind() == kind::NOT)? la[0] : la.notNode();

  Assert(lb != neg_la);
  Node orderOr = (lb < neg_la) ? lb.orNode(neg_la) : neg_la.orNode(lb);
  out.push_back(orderOr);
}

void mutuallyExclusive(std::vector<Node>& out, ConstraintP a, ConstraintP b){
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
  ConstraintP prev = NullConstraint;
  //get transitive unates
  //Only lower bounds or upperbounds should be done.
  for(; scm_iter != scm_end; ++scm_iter){
    const ValueCollection& vc = scm_iter->second;
    if(vc.hasUpperBound()){
      ConstraintP ub = vc.getUpperBound();
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

  vector<ConstraintP> equalities;

  SortedConstraintMap& scm = getVariableSCM(v);
  SortedConstraintMapConstIterator scm_iter = scm.begin();
  SortedConstraintMapConstIterator scm_end = scm.end();

  for(; scm_iter != scm_end; ++scm_iter){
    const ValueCollection& vc = scm_iter->second;
    if(vc.hasEquality()){
      ConstraintP eq = vc.getEquality();
      if(eq->hasLiteral()){
        equalities.push_back(eq);
      }
    }
  }

  vector<ConstraintP>::const_iterator i, j, eq_end = equalities.end();
  for(i = equalities.begin(); i != eq_end; ++i){
    ConstraintP at_i = *i;
    for(j= i + 1; j != eq_end; ++j){
      ConstraintP at_j = *j;

      mutuallyExclusive(out, at_i, at_j);
    }
  }

  for(i = equalities.begin(); i != eq_end; ++i){
    ConstraintP eq = *i;
    const ValueCollection& vc = eq->getValueCollection();
    Assert(vc.hasEquality() && vc.getEquality()->hasLiteral());

    bool hasLB = vc.hasLowerBound() && vc.getLowerBound()->hasLiteral();
    bool hasUB = vc.hasUpperBound() && vc.getUpperBound()->hasLiteral();

    ConstraintP lb = hasLB ?
      vc.getLowerBound() : eq->getStrictlyWeakerLowerBound(true, false);
    ConstraintP ub = hasUB ?
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

bool ConstraintDatabase::handleUnateProp(ConstraintP ant, ConstraintP cons){
  if(cons->negationHasProof()){
    Debug("arith::unate") << "handleUnate: " << ant << " implies " << cons << endl;
    cons->impliedByUnate(ant, true);
    d_raiseConflict.raiseConflict(cons);
    return true;
  }else if(!cons->isTrue()){
    ++d_statistics.d_unatePropagateImplications;
    Debug("arith::unate") << "handleUnate: " << ant << " implies " << cons << endl;
    cons->impliedByUnate(ant, false);
    cons->tryToPropagate();
    return false;
  } else {
    return false;
  }
}

void ConstraintDatabase::unatePropLowerBound(ConstraintP curr, ConstraintP prev){
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
      ConstraintP lb = vc.getLowerBound();
      if(handleUnateProp(curr, lb)){ return; }
    }
    if(vc.hasDisequality()){
      ConstraintP dis = vc.getDisequality();
      if(handleUnateProp(curr, dis)){ return; }
    }
  }
}

void ConstraintDatabase::unatePropUpperBound(ConstraintP curr, ConstraintP prev){
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
      ConstraintP ub = vc.getUpperBound();
      if(handleUnateProp(curr, ub)){ return; }
    }
    if(vc.hasDisequality()){
      ConstraintP dis = vc.getDisequality();
      if(handleUnateProp(curr, dis)){ return; }
    }
  }
}

void ConstraintDatabase::unatePropEquality(ConstraintP curr, ConstraintP prevLB, ConstraintP prevUB){
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
      ConstraintP lb = vc.getLowerBound();
      if(handleUnateProp(curr, lb)){ return; }
    }
    if(vc.hasDisequality()){
      ConstraintP dis = vc.getDisequality();
      if(handleUnateProp(curr, dis)){ return; }
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
      ConstraintP ub = vc.getUpperBound();
      if(handleUnateProp(curr, ub)){ return; }
    }
    if(vc.hasDisequality()){
      ConstraintP dis = vc.getDisequality();
      if(handleUnateProp(curr, dis)){ return; }
    }
  }
}

std::pair<int, int> Constraint::unateFarkasSigns(ConstraintCP ca, ConstraintCP cb){
  ConstraintType a = ca->getType();
  ConstraintType b = cb->getType();

  Assert(a != Disequality);
  Assert(b != Disequality);

  int a_sgn = (a == LowerBound) ? -1 : ((a == UpperBound) ? 1 : 0);
  int b_sgn = (b == LowerBound) ? -1 : ((b == UpperBound) ? 1 : 0);

  if(a_sgn == 0 && b_sgn == 0){
    Assert(a == Equality);
    Assert(b == Equality);
    Assert(ca->getValue() != cb->getValue());
    if(ca->getValue() < cb->getValue()){
      a_sgn = 1;
      b_sgn = -1;
    }else{
      a_sgn = -1;
      b_sgn = 1;
    }
  }else if(a_sgn == 0){
    Assert(b_sgn != 0);
    Assert(a == Equality);
    a_sgn = -b_sgn;
  }else if(b_sgn == 0){
    Assert(a_sgn != 0);
    Assert(b == Equality);
    b_sgn = -a_sgn;
  }
  Assert(a_sgn != 0);
  Assert(b_sgn != 0);

  Debug("arith::unateFarkasSigns") << "Constraint::unateFarkasSigns("<<a <<", " << b << ") -> "
                                   << "("<<a_sgn<<", "<< b_sgn <<")"<< endl;
  return make_pair(a_sgn, b_sgn);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
