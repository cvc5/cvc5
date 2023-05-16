/******************************************************************************
 * Top contributors (to current version):
 *   Tim King, Andres Noetzli, Andrew Reynolds
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

#include "theory/arith/linear/infer_bounds.h"
#include "theory/rewriter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

using namespace inferbounds;

InferBoundAlgorithm::InferBoundAlgorithm()
  : d_alg(None)
{}

InferBoundAlgorithm::InferBoundAlgorithm(Algorithms a)
  : d_alg(a)
{
  Assert(a != Simplex);
}

InferBoundAlgorithm::InferBoundAlgorithm(
    const std::optional<int>& simplexRounds)
    : d_alg(Simplex)
{}

Algorithms InferBoundAlgorithm::getAlgorithm() const{
  return d_alg;
}

const std::optional<int>& InferBoundAlgorithm::getSimplexRounds() const
{
  Assert(getAlgorithm() == Simplex);
  return d_simplexRounds;
}

InferBoundAlgorithm InferBoundAlgorithm::mkLookup(){
  return InferBoundAlgorithm(Lookup);
}

InferBoundAlgorithm InferBoundAlgorithm::mkRowSum(){
  return InferBoundAlgorithm(RowSum);
}

InferBoundAlgorithm InferBoundAlgorithm::mkSimplex(
    const std::optional<int>& rounds)
{
  return InferBoundAlgorithm(rounds);
}

ArithEntailmentCheckParameters::ArithEntailmentCheckParameters()
    : d_algorithms()
{}

ArithEntailmentCheckParameters::~ArithEntailmentCheckParameters()
{}


void ArithEntailmentCheckParameters::addLookupRowSumAlgorithms(){
  addAlgorithm(InferBoundAlgorithm::mkLookup());
  addAlgorithm(InferBoundAlgorithm::mkRowSum());
}

void ArithEntailmentCheckParameters::addAlgorithm(const inferbounds::InferBoundAlgorithm& alg){
  d_algorithms.push_back(alg);
}

ArithEntailmentCheckParameters::const_iterator ArithEntailmentCheckParameters::begin() const{
  return d_algorithms.begin();
}

ArithEntailmentCheckParameters::const_iterator ArithEntailmentCheckParameters::end() const{
  return d_algorithms.end();
}

InferBoundsResult::InferBoundsResult()
  : d_foundBound(false)
  , d_budgetExhausted(false)
  , d_boundIsProvenOpt(false)
  , d_inconsistentState(false)
  , d_reachedThreshold(false)
  , d_value(false)
  , d_term(Node::null())
  , d_upperBound(true)
  , d_explanation(Node::null())
{}

InferBoundsResult::InferBoundsResult(Node term, bool ub)
  : d_foundBound(false)
  , d_budgetExhausted(false)
  , d_boundIsProvenOpt(false)
  , d_inconsistentState(false)
  , d_reachedThreshold(false)
  , d_value(false)
  , d_term(term)
  , d_upperBound(ub)
  , d_explanation(Node::null())
{}

bool InferBoundsResult::foundBound() const {
  return d_foundBound;
}
bool InferBoundsResult::boundIsOptimal() const {
  return d_boundIsProvenOpt;
}
bool InferBoundsResult::inconsistentState() const {
  return d_inconsistentState;
}

bool InferBoundsResult::boundIsInteger() const{
  return foundBound() && d_value.isIntegral();
}

bool InferBoundsResult::boundIsRational() const {
  return foundBound() && d_value.infinitesimalIsZero();
}

Integer InferBoundsResult::valueAsInteger() const{
  Assert(boundIsInteger());
  return getValue().floor();
}
const Rational& InferBoundsResult::valueAsRational() const{
  Assert(boundIsRational());
  return getValue().getNoninfinitesimalPart();
}

const DeltaRational& InferBoundsResult::getValue() const{
  return d_value;
}

Node InferBoundsResult::getTerm() const { return d_term; }

Node InferBoundsResult::getLiteral() const{
  const Rational& q = getValue().getNoninfinitesimalPart();
  NodeManager* nm = NodeManager::currentNM();
  Node qnode = nm->mkConstReal(q);

  Kind k;
  if(d_upperBound){
    // x <= q + c*delta
    Assert(getValue().infinitesimalSgn() <= 0);
    k = boundIsRational() ? kind::LEQ : kind::LT;
  }else{
    // x >= q + c*delta
    Assert(getValue().infinitesimalSgn() >= 0);
    k = boundIsRational() ? kind::GEQ : kind::GT;
  }
  return nm->mkNode(k, getTerm(), qnode);
}

/* If there is a bound, this is a node that explains the bound. */
Node InferBoundsResult::getExplanation() const{
  return d_explanation;
}


void InferBoundsResult::setBound(const DeltaRational& dr, Node exp){
  d_foundBound = true;
  d_value = dr;
  d_explanation = exp;
}

void InferBoundsResult::setBudgetExhausted() { d_budgetExhausted = true; }
void InferBoundsResult::setReachedThreshold() { d_reachedThreshold = true; }
void InferBoundsResult::setIsOptimal() { d_boundIsProvenOpt = true; }
void InferBoundsResult::setInconsistent() { d_inconsistentState = true; }

bool InferBoundsResult::thresholdWasReached() const{
  return d_reachedThreshold;
}
bool InferBoundsResult::budgetIsExhausted() const{
  return d_budgetExhausted;
}

std::ostream& operator<<(std::ostream& os, const InferBoundsResult& ibr){
  os << "{InferBoundsResult " << std::endl;
  os << "on " << ibr.getTerm() << ", ";
  if(ibr.findUpperBound()){
    os << "find upper bound, ";
  }else{
    os << "find lower bound, ";
  }
  if(ibr.foundBound()){
    os << "found a bound: ";
    if(ibr.boundIsInteger()){
      os << ibr.valueAsInteger() << "(int), ";
    }else if(ibr.boundIsRational()){
      os << ibr.valueAsRational() << "(rat), ";
    }else{
      os << ibr.getValue() << "(extended), ";
    }

    os << "as term " << ibr.getLiteral() << ", ";
    os << "explanation " << ibr.getExplanation() << ", ";
  }else {
    os << "did not find a bound, ";
  }

  if(ibr.boundIsOptimal()){
    os << "(opt), ";
  }

  if(ibr.inconsistentState()){
    os << "(inconsistent), ";
  }
  if(ibr.budgetIsExhausted()){
    os << "(budget exhausted), ";
  }
  if(ibr.thresholdWasReached()){
    os << "(reached threshold), ";
  }
  os << "}";
  return os;
}

ArithEntailmentCheckSideEffects::ArithEntailmentCheckSideEffects()
    : d_simplexSideEffects(NULL)
{}

ArithEntailmentCheckSideEffects::~ArithEntailmentCheckSideEffects(){
  if(d_simplexSideEffects != NULL){
    delete d_simplexSideEffects;
    d_simplexSideEffects = NULL;
  }
}

InferBoundsResult& ArithEntailmentCheckSideEffects::getSimplexSideEffects(){
  if(d_simplexSideEffects == NULL){
    d_simplexSideEffects = new InferBoundsResult;
  }
  return *d_simplexSideEffects;
}

namespace inferbounds { /* namespace arith */

std::ostream& operator<<(std::ostream& os,  const Algorithms a){
  switch(a){
  case None:    os << "AlgNone"; break;
  case Lookup:  os << "AlgLookup"; break;
  case RowSum:  os << "AlgRowSum"; break;
  case Simplex: os << "AlgSimplex"; break;
  default:
    Unhandled();
  }

  return os;
}

} /* namespace inferbounds */

} /* namespace arith */
} /* namespace theory */
}  // namespace cvc5::internal
