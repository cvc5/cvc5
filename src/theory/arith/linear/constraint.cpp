/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Alex Ozdemir, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * [[ Add one-line brief description here ]]
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */
#include "theory/arith/linear/constraint.h"

#include <algorithm>
#include <ostream>
#include <unordered_set>

#include "base/output.h"
#include "options/smt_options.h"
#include "proof/eager_proof_generator.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/linear/congruence_manager.h"
#include "theory/arith/linear/normal_form.h"
#include "theory/arith/linear/partial_model.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter.h"

using namespace std;
using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

ConstraintRule::ConstraintRule()
    : d_constraint(NullConstraint),
      d_proofType(NoAP),
      d_antecedentEnd(AntecedentIdSentinel)
{
  d_farkasCoefficients = RationalVectorCPSentinel;
}

ConstraintRule::ConstraintRule(ConstraintP con, ArithProofType pt)
    : d_constraint(con), d_proofType(pt), d_antecedentEnd(AntecedentIdSentinel)
{
  d_farkasCoefficients = RationalVectorCPSentinel;
}
ConstraintRule::ConstraintRule(ConstraintP con,
                               ArithProofType pt,
                               AntecedentId antecedentEnd)
    : d_constraint(con), d_proofType(pt), d_antecedentEnd(antecedentEnd)
{
  d_farkasCoefficients = RationalVectorCPSentinel;
}

ConstraintRule::ConstraintRule(ConstraintP con,
                               ArithProofType pt,
                               AntecedentId antecedentEnd,
                               RationalVectorCP coeffs)
    : d_constraint(con), d_proofType(pt), d_antecedentEnd(antecedentEnd)
{
  Assert(con->isProofProducing() || coeffs == RationalVectorCPSentinel);
  d_farkasCoefficients = coeffs;
}

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

Constraint::Constraint(ArithVar x,
                       ConstraintType t,
                       const DeltaRational& v,
                       bool produceProofs)
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
      d_variablePosition(),
      d_produceProofs(produceProofs)
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
  Trace("arith::constraint") << "push_into " << *this << endl;
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
    Trace("arith::constraint") << "removing" << vc << endl;

    vc.remove(getType());

    if(vc.empty()){
      Trace("arith::constraint") << "erasing" << vc << endl;
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
  Trace("getCeiling") << "Constraint_::getCeiling on " << *this << endl;
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

  if(TraceIsOn("constraint::conflictCommit") && nowInConflict ){
    Trace("constraint::conflictCommit") << "inConflict@setAssertedToTheTheory";
    Trace("constraint::conflictCommit") << "\t" << this << std::endl;
    Trace("constraint::conflictCommit") << "\t" << getNegation() << std::endl;
    Trace("constraint::conflictCommit") << "\t" << getNegation()->externalExplainByAssertions() << std::endl;

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

TrustNode Constraint::externalExplainByAssertions() const
{
  NodeBuilder nb(kind::AND);
  auto pfFromAssumptions = externalExplain(nb, AssertionOrderSentinel);
  Node exp = mkAndFromBuilder(nb);
  if (d_database->isProofEnabled())
  {
    std::vector<Node> assumptions;
    if (exp.getKind() == Kind::AND)
    {
      assumptions.insert(assumptions.end(), exp.begin(), exp.end());
    }
    else
    {
      assumptions.push_back(exp);
    }
    auto pf = d_database->d_pnm->mkScope(pfFromAssumptions, assumptions);
    return d_database->d_pfGen->mkTrustedPropagation(
        getLiteral(), NodeManager::currentNM()->mkAnd(assumptions), pf);
  }
  return TrustNode::mkTrustPropExp(getLiteral(), exp);
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
  Trace("constraints::hsfp") << "hasSimpleFarkasProof " << this << std::endl;
  if (!hasFarkasProof())
  {
    Trace("constraints::hsfp") << "There is no simple Farkas proof because "
                                  "there is no farkas proof."
                               << std::endl;
    return false;
  }

  // For each antecdent ...
  AntecedentId i = getConstraintRule().d_antecedentEnd;
  for (ConstraintCP a = d_database->getAntecedent(i); a != NullConstraint;
       a = d_database->getAntecedent(--i))
  {
    // ... that antecdent must be an assumption OR a tightened assumption ...
    if (a->isPossiblyTightenedAssumption())
    {
      continue;
    }

    // ... otherwise, we do not have a simple Farkas proof.
    if (TraceIsOn("constraints::hsfp"))
    {
      Trace("constraints::hsfp") << "There is no simple Farkas proof b/c there "
                                    "is an antecdent w/ rule ";
      a->getConstraintRule().print(Trace("constraints::hsfp"), d_produceProofs);
      Trace("constraints::hsfp") << std::endl;
    }

    return false;
  }
  return true;
}

bool Constraint::isPossiblyTightenedAssumption() const
{
  // ... that antecdent must be an assumption ...

  if (isAssumption()) return true;
  if (!hasIntTightenProof()) return false;
  if (getConstraintRule().d_antecedentEnd == AntecedentIdSentinel) return false;
  return d_database->getAntecedent(getConstraintRule().d_antecedentEnd)
      ->isAssumption();
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
  if (d_produceProofs)
  {
    const ConstraintRule& rule = getConstraintRule();
    out << std::string(2 * depth, ' ') << "* " << getVariable() << " [";
    out << getProofLiteral();
    if (assertedToTheTheory())
    {
      out << " | wit: " << getWitness();
    }
    out << "]" << ' ' << getType() << ' ' << getValue() << " ("
        << getProofType() << ")";
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

    for (AntecedentId i = rule.d_antecedentEnd; i != AntecedentIdSentinel; --i)
    {
      ConstraintCP antecdent = d_database->getAntecedent(i);
      if (antecdent == NullConstraint)
      {
        break;
      }
      antecdent->printProofTree(out, depth + 1);
    }
    return;
  }
  out << "Cannot print proof. This is not a proof build." << endl;
}

bool Constraint::sanityChecking(Node n) const {
  Comparison cmp = Comparison::parseNormalForm(n);
  Kind k = cmp.comparisonKind();
  Polynomial pleft = cmp.normalizedVariablePart();
  Assert(k == EQUAL || k == DISTINCT || pleft.leadingCoefficientIsPositive());
  Assert(k != EQUAL
         || Monomial::isMember(n[0].getKind() == TO_REAL ? n[0][0] : n[0]));
  Assert(k != DISTINCT
         || Monomial::isMember(n[0][0].getKind() == TO_REAL ? n[0][0][0]
                                                            : n[0][0]));

  TNode left = pleft.getNode();
  DeltaRational right = cmp.normalizedDeltaRational();

  const ArithVariables& avariables = d_database->getArithVariables();

  Trace("Constraint::sanityChecking") << cmp.getNode() << endl;
  Trace("Constraint::sanityChecking") << k << endl;
  Trace("Constraint::sanityChecking") << pleft.getNode() << endl;
  Trace("Constraint::sanityChecking") << left << endl;
  Trace("Constraint::sanityChecking") << right << endl;
  Trace("Constraint::sanityChecking") << getValue() << endl;
  Trace("Constraint::sanityChecking") << avariables.hasArithVar(left) << endl;
  Trace("Constraint::sanityChecking") << avariables.asArithVar(left) << endl;
  Trace("Constraint::sanityChecking") << getVariable() << endl;


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

ConstraintCP ConstraintDatabase::getAntecedent (AntecedentId p) const {
  Assert(p < d_antecedents.size());
  return d_antecedents[p];
}

void ConstraintRule::print(std::ostream& out, bool produceProofs) const
{
  RationalVectorCP coeffs = produceProofs ? d_farkasCoefficients : nullptr;
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

  if (!d_produceProofs)
  {
    return cr.d_farkasCoefficients == RationalVectorCPSentinel;
  }
  Assert(d_produceProofs);

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
    Trace("constraints::wffp") << "running sum: " << lhs << " <= " << rhs << endl;

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
  Trace("constraints::wffp") << "final sum: " << lhs << " <= " << rhs << endl;
  // 0 = lhs <= rhs < 0
  return (lhs.isNull() || (Constant::isMember(lhs) && Constant(lhs).isZero()))
         && rhs.sgn() < 0;
}

ConstraintP Constraint::makeNegation(ArithVar v,
                                     ConstraintType t,
                                     const DeltaRational& r,
                                     bool produceProofs)
{
  switch(t){
  case LowerBound:
    {
      Assert(r.infinitesimalSgn() >= 0);
      if(r.infinitesimalSgn() > 0){
        Assert(r.getInfinitesimalPart() == 1);
        // make (not (v > r)), which is (v <= r)
        DeltaRational dropInf(r.getNoninfinitesimalPart(), 0);
        return new Constraint(v, UpperBound, dropInf, produceProofs);
      }else{
        Assert(r.infinitesimalSgn() == 0);
        // make (not (v >= r)), which is (v < r)
        DeltaRational addInf(r.getNoninfinitesimalPart(), -1);
        return new Constraint(v, UpperBound, addInf, produceProofs);
      }
    }
  case UpperBound:
    {
      Assert(r.infinitesimalSgn() <= 0);
      if(r.infinitesimalSgn() < 0){
        Assert(r.getInfinitesimalPart() == -1);
        // make (not (v < r)), which is (v >= r)
        DeltaRational dropInf(r.getNoninfinitesimalPart(), 0);
        return new Constraint(v, LowerBound, dropInf, produceProofs);
      }else{
        Assert(r.infinitesimalSgn() == 0);
        // make (not (v <= r)), which is (v > r)
        DeltaRational addInf(r.getNoninfinitesimalPart(), 1);
        return new Constraint(v, LowerBound, addInf, produceProofs);
      }
    }
    case Equality: return new Constraint(v, Disequality, r, produceProofs);
    case Disequality: return new Constraint(v, Equality, r, produceProofs);
    default: Unreachable(); return NullConstraint;
  }
}

ConstraintDatabase::ConstraintDatabase(Env& env,
                                       const ArithVariables& avars,
                                       ArithCongruenceManager& cm,
                                       RaiseConflict raiseConflict,
                                       EagerProofGenerator* pfGen)
    : EnvObj(env),
      d_varDatabases(),
      d_toPropagate(context()),
      d_antecedents(context(), false),
      d_watches(new Watches(context(), userContext())),
      d_avariables(avars),
      d_congruenceManager(cm),
      d_pfGen(pfGen),
      d_pnm(d_env.isTheoryProofProducing() ? d_env.getProofNodeManager()
                                           : nullptr),
      d_raiseConflict(raiseConflict),
      d_one(1),
      d_negOne(-1),
      d_statistics(statisticsRegistry())
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
    ConstraintP c = new Constraint(v, t, r, options().smt.produceProofs);
    ConstraintP negC =
        Constraint::makeNegation(v, t, r, options().smt.produceProofs);

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

ConstraintDatabase::Statistics::Statistics(StatisticsRegistry& sr)
    : d_unatePropagateCalls(
        sr.registerInt("theory::arith::cd::unatePropagateCalls")),
      d_unatePropagateImplications(
          sr.registerInt("theory::arith::cd::unatePropagateImplications"))
{
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
    Trace("arith::constraint") << "about to fail" << v << " " << d_varDatabases.size() << endl;
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

TrustNode Constraint::split()
{
  Assert(isEquality() || isDisequality());

  bool isEq = isEquality();

  ConstraintP eq = isEq ? this : d_negation;
  ConstraintP diseq = isEq ? d_negation : this;

  TNode eqNode = eq->getLiteral();
  Assert(eqNode.getKind() == kind::EQUAL);
  TNode lhs = eqNode[0];
  TNode rhs = eqNode[1];

  Node leqNode = NodeBuilder(kind::LEQ) << lhs << rhs;
  Node ltNode = NodeBuilder(kind::LT) << lhs << rhs;
  Node gtNode = NodeBuilder(kind::GT) << lhs << rhs;
  Node geqNode = NodeBuilder(kind::GEQ) << lhs << rhs;

  Node lemma = NodeBuilder(OR) << leqNode << geqNode;

  TrustNode trustedLemma;
  if (d_database->isProofEnabled())
  {
    TypeNode type = lhs.getType();
    // Farkas proof that this works.
    auto nm = NodeManager::currentNM();
    auto nLeqPf = d_database->d_pnm->mkAssume(leqNode.negate());
    auto gtPf = d_database->d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM, {nLeqPf}, {gtNode});
    auto nGeqPf = d_database->d_pnm->mkAssume(geqNode.negate());
    auto ltPf = d_database->d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM, {nGeqPf}, {ltNode});
    auto sumPf =
        d_database->d_pnm->mkNode(PfRule::MACRO_ARITH_SCALE_SUM_UB,
                                  {gtPf, ltPf},
                                  {nm->mkConstRealOrInt(type, Rational(-1)),
                                   nm->mkConstRealOrInt(type, Rational(1))});
    auto botPf = d_database->d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM, {sumPf}, {nm->mkConst(false)});
    std::vector<Node> a = {leqNode.negate(), geqNode.negate()};
    auto notAndNotPf = d_database->d_pnm->mkScope(botPf, a);
    // No need to ensure that the expected node aggrees with `a` because we are
    // not providing an expected node.
    auto orNotNotPf =
        d_database->d_pnm->mkNode(PfRule::NOT_AND, {notAndNotPf}, {});
    auto orPf = d_database->d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM, {orNotNotPf}, {lemma});
    trustedLemma = d_database->d_pfGen->mkTrustNode(lemma, orPf);
  }
  else
  {
    trustedLemma = TrustNode::mkTrustLemma(lemma);
  }

  eq->d_database->pushSplitWatch(eq);
  diseq->d_database->pushSplitWatch(diseq);

  return trustedLemma;
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

  ConstraintP posC =
      new Constraint(v, posType, posDR, options().smt.produceProofs);

  Trace("arith::constraint") << "addliteral( literal ->" << literal << ")" << endl;
  Trace("arith::constraint") << "addliteral( posC ->" << posC << ")" << endl;

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
    Trace("arith::constraint") << "hit " << hit << endl;
    Trace("arith::constraint") << "posC " << posC << endl;

    delete posC;

    hit->setLiteral(atomNode);
    hit->getNegation()->setLiteral(negationNode);
    return isNot ? hit->getNegation(): hit;
  }else{
    Comparison negCmp = Comparison::parseNormalForm(negationNode);

    ConstraintType negType = Constraint::constraintTypeOfComparison(negCmp);
    DeltaRational negDR = negCmp.normalizedDeltaRational();

    ConstraintP negC =
        new Constraint(v, negType, negDR, options().smt.produceProofs);

    SortedConstraintMapIterator negI;

    if(posC->isEquality()){
      negI = posI;
    }else{
      Assert(posC->isLowerBound() || posC->isUpperBound());

      pair<SortedConstraintMapIterator, bool> negInsertAttempt;
      negInsertAttempt = scm.insert(make_pair(negC->getValue(), ValueCollection()));

      Trace("nf::tmp") << "sdhjfgdhjkldfgljkhdfg" << endl;
      Trace("nf::tmp") << negC << endl;
      Trace("nf::tmp") << negC->getValue() << endl;

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
  Trace("constraints::pf") << "setAssumption(" << this << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(hasLiteral());
  Assert(assertedToTheTheory());

  d_database->pushConstraintRule(ConstraintRule(this, AssumeAP));

  Assert(inConflict() == nowInConflict);
  if(TraceIsOn("constraint::conflictCommit") && inConflict()){
    Trace("constraint::conflictCommit") << "inConflict@setAssumption " << this << std::endl;
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
  Trace("constraints::pf") << "impliedByUnate(" << this << ", " << *imp << ")" << std::endl;
  Assert(!hasProof());
  Assert(imp->hasProof());
  Assert(negationHasProof() == nowInConflict);

  d_database->d_antecedents.push_back(NullConstraint);
  d_database->d_antecedents.push_back(imp);

  AntecedentId antecedentEnd = d_database->d_antecedents.size() - 1;

  RationalVectorP coeffs;
  if (d_produceProofs)
  {
    std::pair<int, int> sgns = unateFarkasSigns(getNegation(), imp);

    Rational first(sgns.first);
    Rational second(sgns.second);

    coeffs = new RationalVector();
    coeffs->push_back(first);
    coeffs->push_back(second);
  }
  else
  {
    coeffs = RationalVectorPSentinel;
  }
  // no need to delete coeffs the memory is owned by ConstraintRule
  d_database->pushConstraintRule(ConstraintRule(this, FarkasAP, antecedentEnd, coeffs));

  Assert(inConflict() == nowInConflict);
  if(TraceIsOn("constraint::conflictCommit") && inConflict()){
    Trace("constraint::conflictCommit") << "inConflict@impliedByUnate " << this << std::endl;
  }

  if(TraceIsOn("constraints::wffp") && !wellFormedFarkasProof()){
    getConstraintRule().print(Trace("constraints::wffp"), d_produceProofs);
  }
  Assert(wellFormedFarkasProof());
}

void Constraint::impliedByTrichotomy(ConstraintCP a, ConstraintCP b, bool nowInConflict){
  Trace("constraints::pf") << "impliedByTrichotomy(" << this << ", " << *a << ", ";
  Trace("constraints::pf") << *b << ")" << std::endl;
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
  if(TraceIsOn("constraint::conflictCommit") && inConflict()){
    Trace("constraint::conflictCommit") << "inConflict@impliedByTrichotomy " << this << std::endl;
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
  Trace("constraints::pf") << "impliedByIntTighten(" << this << ", " << *a << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(a->hasProof());
  Trace("pf::arith") << "impliedByIntTighten(" << this << ", " << a << ")"
                     << std::endl;

  d_database->d_antecedents.push_back(NullConstraint);
  d_database->d_antecedents.push_back(a);
  AntecedentId antecedentEnd = d_database->d_antecedents.size() - 1;
  d_database->pushConstraintRule(ConstraintRule(this, IntTightenAP, antecedentEnd));

  Assert(inConflict() == nowInConflict);
  if(inConflict()){
    Trace("constraint::conflictCommit") << "inConflict impliedByIntTighten" << this << std::endl;
  }
}

void Constraint::impliedByIntHole(ConstraintCP a, bool nowInConflict){
  Trace("constraints::pf") << "impliedByIntHole(" << this << ", " << *a << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(a->hasProof());
  Trace("pf::arith") << "impliedByIntHole(" << this << ", " << a << ")"
                     << std::endl;

  d_database->d_antecedents.push_back(NullConstraint);
  d_database->d_antecedents.push_back(a);
  AntecedentId antecedentEnd = d_database->d_antecedents.size() - 1;
  d_database->pushConstraintRule(ConstraintRule(this, IntHoleAP, antecedentEnd));

  Assert(inConflict() == nowInConflict);
  if(TraceIsOn("constraint::conflictCommit") && inConflict()){
    Trace("constraint::conflictCommit") << "inConflict impliedByIntHole" << this << std::endl;
  }
}

void Constraint::impliedByIntHole(const ConstraintCPVec& b, bool nowInConflict){
  Trace("constraints::pf") << "impliedByIntHole(" << this;
  if (TraceIsOn("constraints::pf")) {
    for (const ConstraintCP& p : b)
    {
      Trace("constraints::pf") << ", " << p;
    }
  }
  Trace("constraints::pf") << ")" << std::endl;

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
  if(TraceIsOn("constraint::conflictCommit") && inConflict()){
    Trace("constraint::conflictCommit") << "inConflict@impliedByIntHole[vec] " << this << std::endl;
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
  Trace("constraints::pf") << "impliedByFarkas(" << this;
  if (TraceIsOn("constraints::pf")) {
    for (const ConstraintCP& p : a)
    {
      Trace("constraints::pf") << ", " << p;
    }
  }
  Trace("constraints::pf") << ", <coeffs>";
  Trace("constraints::pf") << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(allHaveProof(a));

  Assert(d_produceProofs == (coeffs != RationalVectorCPSentinel));
  Assert(!d_produceProofs || coeffs->size() == a.size() + 1);

  Assert(a.size() >= 1);

  d_database->d_antecedents.push_back(NullConstraint);
  for(ConstraintCPVec::const_iterator i = a.begin(), end = a.end(); i != end; ++i){
    ConstraintCP c_i = *i;
    Assert(c_i->hasProof());
    d_database->d_antecedents.push_back(c_i);
  }
  AntecedentId antecedentEnd = d_database->d_antecedents.size() - 1;

  RationalVectorCP coeffsCopy;
  if (d_produceProofs)
  {
    Assert(coeffs != RationalVectorCPSentinel);
    coeffsCopy = new RationalVector(*coeffs);
  }
  else
  {
    coeffsCopy = RationalVectorCPSentinel;
  }
  d_database->pushConstraintRule(ConstraintRule(this, FarkasAP, antecedentEnd, coeffsCopy));

  Assert(inConflict() == nowInConflict);
  if(TraceIsOn("constraint::conflictCommit") && inConflict()){
    Trace("constraint::conflictCommit") << "inConflict@impliedByFarkas " << this << std::endl;
  }
  if(TraceIsOn("constraints::wffp") && !wellFormedFarkasProof()){
    getConstraintRule().print(Trace("constraints::wffp"), d_produceProofs);
  }
  Assert(wellFormedFarkasProof());
}


void Constraint::setInternalAssumption(bool nowInConflict){
  Trace("constraints::pf") << "setInternalAssumption(" << this;
  Trace("constraints::pf") << ")" << std::endl;
  Assert(!hasProof());
  Assert(negationHasProof() == nowInConflict);
  Assert(!assertedToTheTheory());

  d_database->pushConstraintRule(ConstraintRule(this, InternalAssumeAP));

  Assert(inConflict() == nowInConflict);
  if(TraceIsOn("constraint::conflictCommit") && inConflict()){
    Trace("constraint::conflictCommit") << "inConflict@setInternalAssumption " << this << std::endl;
  }
}


void Constraint::setEqualityEngineProof(){
  Trace("constraints::pf") << "setEqualityEngineProof(" << this;
  Trace("constraints::pf") << ")" << std::endl;
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

TrustNode Constraint::externalExplainForPropagation(TNode lit) const
{
  Assert(hasProof());
  Assert(!isAssumption());
  Assert(!isInternalAssumption());
  NodeBuilder nb(Kind::AND);
  auto pfFromAssumptions = externalExplain(nb, d_assertionOrder);
  Node n = mkAndFromBuilder(nb);
  if (d_database->isProofEnabled())
  {
    std::vector<Node> assumptions;
    if (n.getKind() == Kind::AND)
    {
      assumptions.insert(assumptions.end(), n.begin(), n.end());
    }
    else
    {
      assumptions.push_back(n);
    }
    if (getProofLiteral() != lit)
    {
      pfFromAssumptions = d_database->d_pnm->mkNode(
          PfRule::MACRO_SR_PRED_TRANSFORM, {pfFromAssumptions}, {lit});
    }
    auto pf = d_database->d_pnm->mkScope(pfFromAssumptions, assumptions);
    return d_database->d_pfGen->mkTrustedPropagation(
        lit, NodeManager::currentNM()->mkAnd(assumptions), pf);
  }
  else
  {
    return TrustNode::mkTrustPropExp(lit, n);
  }
}

TrustNode Constraint::externalExplainConflict() const
{
  Trace("pf::arith::explain") << this << std::endl;
  Assert(inConflict());
  NodeBuilder nb(kind::AND);
  auto pf1 = externalExplainByAssertions(nb);
  auto not2 = getNegation()->getProofLiteral().negate();
  auto pf2 = getNegation()->externalExplainByAssertions(nb);
  Node n = mkAndFromBuilder(nb);
  if (d_database->isProofEnabled())
  {
    auto pfNot2 = d_database->d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM, {pf1}, {not2});
    std::vector<Node> lits;
    if (n.getKind() == Kind::AND)
    {
      lits.insert(lits.end(), n.begin(), n.end());
    }
    else
    {
      lits.push_back(n);
    }
    if (TraceIsOn("arith::pf::externalExplainConflict"))
    {
      Trace("arith::pf::externalExplainConflict") << "Lits:" << std::endl;
      for (const auto& l : lits)
      {
        Trace("arith::pf::externalExplainConflict") << "  : " << l << std::endl;
      }
    }
    std::vector<Node> contraLits = {getProofLiteral(),
                                    getNegation()->getProofLiteral()};
    auto bot =
        not2.getKind() == Kind::NOT
            ? d_database->d_pnm->mkNode(PfRule::CONTRA, {pf2, pfNot2}, {})
            : d_database->d_pnm->mkNode(PfRule::CONTRA, {pfNot2, pf2}, {});
    if (TraceIsOn("arith::pf::tree"))
    {
      Trace("arith::pf::tree") << *this << std::endl;
      Trace("arith::pf::tree") << *getNegation() << std::endl;
      Trace("arith::pf::tree") << "\n\nTree:\n";
      printProofTree(Trace("arith::pf::tree"));
      getNegation()->printProofTree(Trace("arith::pf::tree"));
    }
    auto confPf = d_database->d_pnm->mkScope(bot, lits);
    return d_database->d_pfGen->mkTrustNode(
        NodeManager::currentNM()->mkAnd(lits), confPf, true);
  }
  else
  {
    return TrustNode::mkTrustConflict(n);
  }
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
  NodeBuilder nb(kind::AND);
  ConstraintCPVec::const_iterator i, end;
  for(i = v.begin(), end = v.end(); i != end; ++i){
    ConstraintCP v_i = *i;
    v_i->externalExplain(nb, order);
  }
  return mkAndFromBuilder(nb);
}

std::shared_ptr<ProofNode> Constraint::externalExplain(
    NodeBuilder& nb, AssertionOrder order) const
{
  if (TraceIsOn("pf::arith::explain"))
  {
    this->printProofTree(Trace("arith::pf::tree"));
    Trace("pf::arith::explain") << "Explaining: " << this << " with rule ";
    getConstraintRule().print(Trace("pf::arith::explain"), d_produceProofs);
    Trace("pf::arith::explain") << std::endl;
  }
  Assert(hasProof());
  Assert(!isAssumption() || assertedToTheTheory());
  Assert(!isInternalAssumption());
  std::shared_ptr<ProofNode> pf{};

  ProofNodeManager* pnm = d_database->d_pnm;

  if (assertedBefore(order))
  {
    Trace("pf::arith::explain") << "  already asserted" << std::endl;
    nb << getWitness();
    if (d_database->isProofEnabled())
    {
      pf = pnm->mkAssume(getWitness());
      // If the witness and literal differ, prove the difference through a
      // rewrite.
      if (getWitness() != getProofLiteral())
      {
        pf = pnm->mkNode(
            PfRule::MACRO_SR_PRED_TRANSFORM, {pf}, {getProofLiteral()});
      }
    }
  }
  else if (hasEqualityEngineProof())
  {
    // just assume, it will be explained again
    Node lit = getLiteral();
    if (d_database->isProofEnabled())
    {
      std::shared_ptr<ProofNode> a = pnm->mkAssume(getLiteral());
      pf = pnm->mkNode(
          PfRule::MACRO_SR_PRED_TRANSFORM, {a}, {getProofLiteral()});
    }
    Assert(lit.getKind() != kind::AND);
    nb << lit;
  }
  else
  {
    Trace("pf::arith::explain") << "  recursion!" << std::endl;
    Assert(!isAssumption());
    AntecedentId p = getEndAntecedent();
    ConstraintCP antecedent = d_database->d_antecedents[p];
    std::vector<std::shared_ptr<ProofNode>> children;

    while (antecedent != NullConstraint)
    {
      Trace("pf::arith::explain") << "Explain " << antecedent << std::endl;
      auto pn = antecedent->externalExplain(nb, order);
      if (d_database->isProofEnabled())
      {
        children.push_back(pn);
      }
      --p;
      antecedent = d_database->d_antecedents[p];
    }

    if (d_database->isProofEnabled())
    {
      switch (getProofType())
      {
        case ArithProofType::AssumeAP:
        case ArithProofType::EqualityEngineAP:
        {
          Unreachable() << "These should be handled above";
          break;
        }
        case ArithProofType::FarkasAP:
        {
          // Per docs in constraint.h,
          // the 0th farkas coefficient is for the negation of the deduced
          // constraint the 1st corresponds to the last antecedent the nth
          // corresponds to the first antecedent Then, the farkas coefficients
          // and the antecedents are in the same order.

          // Enumerate child proofs (negation included) in d_farkasCoefficients
          // order
          Node plit = getNegation()->getProofLiteral();
          std::vector<std::shared_ptr<ProofNode>> farkasChildren;
          farkasChildren.push_back(pnm->mkAssume(plit));
          farkasChildren.insert(
              farkasChildren.end(), children.rbegin(), children.rend());

          NodeManager* nm = NodeManager::currentNM();

          // Enumerate d_farkasCoefficients as nodes.
          std::vector<Node> farkasCoeffs;
          TypeNode type = plit[0].getType();
          for (Rational r : *getFarkasCoefficients())
          {
            farkasCoeffs.push_back(nm->mkConstReal(Rational(r)));
          }

          // Apply the scaled-sum rule.
          std::shared_ptr<ProofNode> sumPf = pnm->mkNode(
              PfRule::MACRO_ARITH_SCALE_SUM_UB, farkasChildren, farkasCoeffs);

          // Provable rewrite the result
          auto botPf = pnm->mkNode(
              PfRule::MACRO_SR_PRED_TRANSFORM, {sumPf}, {nm->mkConst(false)});

          // Scope out the negated constraint, yielding a proof of the
          // constraint.
          std::vector<Node> assump{plit};
          auto maybeDoubleNotPf = pnm->mkScope(botPf, assump, false);

          // No need to ensure that the expected node aggrees with `assump`
          // because we are not providing an expected node.
          //
          // Prove that this is the literal (may need to clean a double-not)
          pf = pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM,
                           {maybeDoubleNotPf},
                           {getProofLiteral()});

          break;
        }
        case ArithProofType::IntTightenAP:
        {
          if (isUpperBound())
          {
            pf = pnm->mkNode(
                PfRule::INT_TIGHT_UB, children, {}, getProofLiteral());
          }
          else if (isLowerBound())
          {
            pf = pnm->mkNode(
                PfRule::INT_TIGHT_LB, children, {}, getProofLiteral());
          }
          else
          {
            Unreachable();
          }
          break;
        }
        case ArithProofType::IntHoleAP:
        {
          Node t =
              builtin::BuiltinProofRuleChecker::mkTheoryIdNode(THEORY_ARITH);
          pf = pnm->mkNode(PfRule::THEORY_INFERENCE,
                           children,
                           {getProofLiteral(), t},
                           getProofLiteral());
          break;
        }
        case ArithProofType::TrichotomyAP:
        {
          pf = pnm->mkNode(PfRule::ARITH_TRICHOTOMY,
                           children,
                           {getProofLiteral()},
                           getProofLiteral());
          break;
        }
        case ArithProofType::InternalAssumeAP:
        case ArithProofType::NoAP:
        default:
        {
          Unreachable() << getProofType()
                        << " should not be visible in explanation";
          break;
        }
      }
    }
  }
  return pf;
}

Node Constraint::externalExplainByAssertions(ConstraintCP a, ConstraintCP b){
  NodeBuilder nb(kind::AND);
  a->externalExplainByAssertions(nb);
  b->externalExplainByAssertions(nb);
  return nb;
}

Node Constraint::externalExplainByAssertions(ConstraintCP a, ConstraintCP b, ConstraintCP c){
  NodeBuilder nb(kind::AND);
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
        Trace("getBestImpliedBound") << fdj++ << " " << r << " " << i->first << endl;
      }else if( (i->first) > r){
        if(i == i_begin){
          return NullConstraint;
        }else{
          --i;
          Trace("getBestImpliedBound") << fdj++ << " " << r << " " << i->first << endl;
        }
      }

      do{
        Trace("getBestImpliedBound") << fdj++ << " " << r << " " << i->first << endl;
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

bool ConstraintDatabase::variableDatabaseIsSetup(ArithVar v) const {
  return v < d_varDatabases.size();
}

ConstraintDatabase::Watches::Watches(context::Context* satContext,
                                     context::Context* userContext)
    : d_constraintProofs(satContext),
      d_canBePropagatedWatches(satContext),
      d_assertionOrderWatches(satContext),
      d_splitWatches(userContext)
{}


void Constraint::setLiteral(Node n) {
  Trace("arith::constraint") << "Mapping " << *this << " to " << n << std::endl;
  Assert(Comparison::isNormalAtom(n));
  Assert(!hasLiteral());
  Assert(sanityChecking(n));
  d_literal = n;
  NodetoConstraintMap& map = d_database->d_nodetoConstraintMap;
  Assert(map.find(n) == map.end());
  map.insert(make_pair(d_literal, this));
}

Node Constraint::getProofLiteral() const
{
  Assert(d_database != nullptr);
  Assert(d_database->d_avariables.hasNode(d_variable));
  Node varPart = d_database->d_avariables.asNode(d_variable);
  Kind cmp;
  bool neg = false;
  switch (d_type)
  {
    case ConstraintType::UpperBound:
    {
      if (d_value.infinitesimalIsZero())
      {
        cmp = Kind::LEQ;
      }
      else
      {
        cmp = Kind::LT;
      }
      break;
    }
    case ConstraintType::LowerBound:
    {
      if (d_value.infinitesimalIsZero())
      {
        cmp = Kind::GEQ;
      }
      else
      {
        cmp = Kind::GT;
      }
      break;
    }
    case ConstraintType::Equality:
    {
      cmp = Kind::EQUAL;
      break;
    }
    case ConstraintType::Disequality:
    {
      cmp = Kind::EQUAL;
      neg = true;
      break;
    }
    default: Unreachable() << d_type;
  }
  NodeManager* nm = NodeManager::currentNM();
  Node constPart = nm->mkConstRealOrInt(
      varPart.getType(), Rational(d_value.getNoninfinitesimalPart()));
  Node posLit = nm->mkNode(cmp, varPart, constPart);
  return neg ? posLit.negate() : posLit;
}

void ConstraintDatabase::proveOr(std::vector<TrustNode>& out,
                                 ConstraintP a,
                                 ConstraintP b,
                                 bool negateSecond) const
{
  Node la = a->getLiteral();
  Node lb = b->getLiteral();
  Node orN = (la < lb) ? la.orNode(lb) : lb.orNode(la);
  if (isProofEnabled())
  {
    Assert(b->getNegation()->getType() != ConstraintType::Disequality);
    auto nm = NodeManager::currentNM();
    Node alit = a->getNegation()->getProofLiteral();
    TypeNode type = alit[0].getType();
    auto pf_neg_la = d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM,
                                   {d_pnm->mkAssume(la.negate())},
                                   {alit});
    Node blit = b->getNegation()->getProofLiteral();
    auto pf_neg_lb = d_pnm->mkNode(PfRule::MACRO_SR_PRED_TRANSFORM,
                                   {d_pnm->mkAssume(lb.negate())},
                                   {blit});
    int sndSign = negateSecond ? -1 : 1;
    auto bot_pf = d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM,
        {d_pnm->mkNode(PfRule::MACRO_ARITH_SCALE_SUM_UB,
                       {pf_neg_la, pf_neg_lb},
                       {nm->mkConstRealOrInt(type, Rational(-1 * sndSign)),
                        nm->mkConstRealOrInt(type, Rational(sndSign))})},
        {nm->mkConst(false)});
    std::vector<Node> as;
    std::transform(orN.begin(), orN.end(), std::back_inserter(as), [](Node n) {
      return n.negate();
    });
    // No need to ensure that the expected node aggrees with `as` because we
    // are not providing an expected node.
    auto pf = d_pnm->mkNode(
        PfRule::MACRO_SR_PRED_TRANSFORM,
        {d_pnm->mkNode(PfRule::NOT_AND, {d_pnm->mkScope(bot_pf, as)}, {})},
        {orN});
    out.push_back(d_pfGen->mkTrustNode(orN, pf));
  }
  else
  {
    out.push_back(TrustNode::mkTrustLemma(orN));
  }
}

void ConstraintDatabase::implies(std::vector<TrustNode>& out,
                                 ConstraintP a,
                                 ConstraintP b) const
{
  Node la = a->getLiteral();
  Node lb = b->getLiteral();

  Node neg_la = (la.getKind() == kind::NOT)? la[0] : la.notNode();

  Assert(lb != neg_la);
  Assert(b->getNegation()->getType() == ConstraintType::LowerBound
         || b->getNegation()->getType() == ConstraintType::UpperBound);
  proveOr(out,
          a->getNegation(),
          b,
          b->getNegation()->getType() == ConstraintType::LowerBound);
}

void ConstraintDatabase::mutuallyExclusive(std::vector<TrustNode>& out,
                                           ConstraintP a,
                                           ConstraintP b) const
{
  Node la = a->getLiteral();
  Node lb = b->getLiteral();

  Node neg_la = la.negate();
  Node neg_lb = lb.negate();
  proveOr(out, a->getNegation(), b->getNegation(), true);
}

void ConstraintDatabase::outputUnateInequalityLemmas(
    std::vector<TrustNode>& out, ArithVar v) const
{
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

void ConstraintDatabase::outputUnateEqualityLemmas(std::vector<TrustNode>& out,
                                                   ArithVar v) const
{
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

void ConstraintDatabase::outputUnateEqualityLemmas(
    std::vector<TrustNode>& lemmas) const
{
  for(ArithVar v = 0, N = d_varDatabases.size(); v < N; ++v){
    outputUnateEqualityLemmas(lemmas, v);
  }
}

void ConstraintDatabase::outputUnateInequalityLemmas(
    std::vector<TrustNode>& lemmas) const
{
  for(ArithVar v = 0, N = d_varDatabases.size(); v < N; ++v){
    outputUnateInequalityLemmas(lemmas, v);
  }
}

bool ConstraintDatabase::handleUnateProp(ConstraintP ant, ConstraintP cons){
  if(cons->negationHasProof()){
    Trace("arith::unate") << "handleUnate: " << ant << " implies " << cons << endl;
    cons->impliedByUnate(ant, true);
    d_raiseConflict.raiseConflict(cons, InferenceId::ARITH_CONF_UNATE_PROP);
    return true;
  }else if(!cons->isTrue()){
    ++d_statistics.d_unatePropagateImplications;
    Trace("arith::unate") << "handleUnate: " << ant << " implies " << cons << endl;
    cons->impliedByUnate(ant, false);
    cons->tryToPropagate();
    return false;
  } else {
    return false;
  }
}

void ConstraintDatabase::unatePropLowerBound(ConstraintP curr, ConstraintP prev){
  Trace("arith::unate") << "unatePropLowerBound " << curr << " " << prev << endl;
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
  Trace("arith::unate") << "unatePropUpperBound " << curr << " " << prev << endl;
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
  Trace("arith::unate") << "unatePropEquality " << curr << " " << prevLB << " " << prevUB << endl;
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

  Trace("arith::unateFarkasSigns") << "Constraint::unateFarkasSigns("<<a <<", " << b << ") -> "
                                   << "("<<a_sgn<<", "<< b_sgn <<")"<< endl;
  return make_pair(a_sgn, b_sgn);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
