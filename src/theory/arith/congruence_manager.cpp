/*********************                                                        */
/*! \file congruence_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Dejan Jovanovic, Morgan Deters, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "theory/arith/congruence_manager.h"

#include "base/output.h"
#include "smt/smt_statistics_registry.h"
#include "theory/arith/arith_utilities.h"
#include "theory/arith/constraint.h"
#include "theory/quantifiers/equality_infer.h"
#include "options/arith_options.h"

namespace CVC4 {
namespace theory {
namespace arith {

ArithCongruenceManager::ArithCongruenceManager(context::Context* c, ConstraintDatabase& cd, SetupLiteralCallBack setup, const ArithVariables& avars, RaiseEqualityEngineConflict raiseConflict)
  : d_inConflict(c),
    d_raiseConflict(raiseConflict),
    d_notify(*this),
    d_eq_infer(NULL),
    d_eqi_counter(0,c),
    d_keepAlive(c),
    d_propagatations(c),
    d_explanationMap(c),
    d_constraintDatabase(cd),
    d_setupLiteral(setup),
    d_avariables(avars),
    d_ee(d_notify, c, "theory::arith::ArithCongruenceManager", true)
{
  //module to infer additional equalities based on normalization
  if( options::sNormInferEq() ){
    d_eq_infer = new quantifiers::EqualityInference(c, true);
    d_true = NodeManager::currentNM()->mkConst( true );
  }
}

ArithCongruenceManager::~ArithCongruenceManager() {
  if( d_eq_infer ){
    delete d_eq_infer;
  }
}

ArithCongruenceManager::Statistics::Statistics():
  d_watchedVariables("theory::arith::congruence::watchedVariables", 0),
  d_watchedVariableIsZero("theory::arith::congruence::watchedVariableIsZero", 0),
  d_watchedVariableIsNotZero("theory::arith::congruence::watchedVariableIsNotZero", 0),
  d_equalsConstantCalls("theory::arith::congruence::equalsConstantCalls", 0),
  d_propagations("theory::arith::congruence::propagations", 0),
  d_propagateConstraints("theory::arith::congruence::propagateConstraints", 0),
  d_conflicts("theory::arith::congruence::conflicts", 0)
{
  smtStatisticsRegistry()->registerStat(&d_watchedVariables);
  smtStatisticsRegistry()->registerStat(&d_watchedVariableIsZero);
  smtStatisticsRegistry()->registerStat(&d_watchedVariableIsNotZero);
  smtStatisticsRegistry()->registerStat(&d_equalsConstantCalls);
  smtStatisticsRegistry()->registerStat(&d_propagations);
  smtStatisticsRegistry()->registerStat(&d_propagateConstraints);
  smtStatisticsRegistry()->registerStat(&d_conflicts);
}

ArithCongruenceManager::Statistics::~Statistics(){
  smtStatisticsRegistry()->unregisterStat(&d_watchedVariables);
  smtStatisticsRegistry()->unregisterStat(&d_watchedVariableIsZero);
  smtStatisticsRegistry()->unregisterStat(&d_watchedVariableIsNotZero);
  smtStatisticsRegistry()->unregisterStat(&d_equalsConstantCalls);
  smtStatisticsRegistry()->unregisterStat(&d_propagations);
  smtStatisticsRegistry()->unregisterStat(&d_propagateConstraints);
  smtStatisticsRegistry()->unregisterStat(&d_conflicts);
}

ArithCongruenceManager::ArithCongruenceNotify::ArithCongruenceNotify(ArithCongruenceManager& acm)
  : d_acm(acm)
{}

bool ArithCongruenceManager::ArithCongruenceNotify::eqNotifyTriggerEquality(TNode equality, bool value) {
  Debug("arith::congruences") << "ArithCongruenceNotify::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false") << ")" << std::endl;
  if (value) {
    return d_acm.propagate(equality);
  } else {
    return d_acm.propagate(equality.notNode());
  }
}
bool ArithCongruenceManager::ArithCongruenceNotify::eqNotifyTriggerPredicate(TNode predicate, bool value) {
  Unreachable();
}

bool ArithCongruenceManager::ArithCongruenceNotify::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
  Debug("arith::congruences") << "ArithCongruenceNotify::eqNotifyTriggerTermEquality(" << t1 << ", " << t2 << ", " << (value ? "true" : "false") << ")" << std::endl;
  if (value) {
    return d_acm.propagate(t1.eqNode(t2));
  } else {
    return d_acm.propagate(t1.eqNode(t2).notNode());
  }
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyConstantTermMerge(TNode t1, TNode t2) {
  Debug("arith::congruences") << "ArithCongruenceNotify::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << std::endl;
  d_acm.propagate(t1.eqNode(t2));
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyNewClass(TNode t) {
  d_acm.eqNotifyNewClass(t);
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyPreMerge(TNode t1, TNode t2) {
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyPostMerge(TNode t1, TNode t2) {
  d_acm.eqNotifyPostMerge(t1,t2);
}
void ArithCongruenceManager::ArithCongruenceNotify::eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {
}

void ArithCongruenceManager::raiseConflict(Node conflict){
  Assert(!inConflict());
  Debug("arith::conflict") << "difference manager conflict   " << conflict << std::endl;
  d_inConflict.raise();
  d_raiseConflict.raiseEEConflict(conflict);
}
bool ArithCongruenceManager::inConflict() const{
  return d_inConflict.isRaised();
}

bool ArithCongruenceManager::hasMorePropagations() const {
  return !d_propagatations.empty();
}
const Node ArithCongruenceManager::getNextPropagation() {
  Assert(hasMorePropagations());
  Node prop = d_propagatations.front();
  d_propagatations.dequeue();
  return prop;
}

bool ArithCongruenceManager::canExplain(TNode n) const {
  return d_explanationMap.find(n) != d_explanationMap.end();
}

void ArithCongruenceManager::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_ee.setMasterEqualityEngine(eq);
}

Node ArithCongruenceManager::externalToInternal(TNode n) const{
  Assert(canExplain(n));
  ExplainMap::const_iterator iter = d_explanationMap.find(n);
  size_t pos = (*iter).second;
  return d_propagatations[pos];
}

void ArithCongruenceManager::pushBack(TNode n){
  d_explanationMap.insert(n, d_propagatations.size());
  d_propagatations.enqueue(n);

  ++(d_statistics.d_propagations);
}
void ArithCongruenceManager::pushBack(TNode n, TNode r){
  d_explanationMap.insert(r, d_propagatations.size());
  d_explanationMap.insert(n, d_propagatations.size());
  d_propagatations.enqueue(n);

  ++(d_statistics.d_propagations);
}
void ArithCongruenceManager::pushBack(TNode n, TNode r, TNode w){
  d_explanationMap.insert(w, d_propagatations.size());
  d_explanationMap.insert(r, d_propagatations.size());
  d_explanationMap.insert(n, d_propagatations.size());
  d_propagatations.enqueue(n);

  ++(d_statistics.d_propagations);
}

void ArithCongruenceManager::watchedVariableIsZero(ConstraintCP lb, ConstraintCP ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());
  Assert(lb->getValue().sgn() == 0);
  Assert(ub->getValue().sgn() == 0);

  ++(d_statistics.d_watchedVariableIsZero);

  ArithVar s = lb->getVariable();
  Node reason = Constraint::externalExplainByAssertions(lb,ub);

  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(true, s, reason);
}

void ArithCongruenceManager::watchedVariableIsZero(ConstraintCP eq){
  Assert(eq->isEquality());
  Assert(eq->getValue().sgn() == 0);

  ++(d_statistics.d_watchedVariableIsZero);

  ArithVar s = eq->getVariable();

  //Explain for conflict is correct as these proofs are generated
  //and stored eagerly
  //These will be safe for propagation later as well
  Node reason = eq->externalExplainByAssertions();

  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(true, s, reason);
}

void ArithCongruenceManager::watchedVariableCannotBeZero(ConstraintCP c){
  ++(d_statistics.d_watchedVariableIsNotZero);

  ArithVar s = c->getVariable();

  //Explain for conflict is correct as these proofs are generated and stored eagerly
  //These will be safe for propagation later as well
  Node reason = c->externalExplainByAssertions();

  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(false, s, reason);
}


bool ArithCongruenceManager::propagate(TNode x){
  Debug("arith::congruenceManager")<< "ArithCongruenceManager::propagate("<<x<<")"<<std::endl;
  if(inConflict()){
    return true;
  }

  Node rewritten = Rewriter::rewrite(x);

  //Need to still propagate this!
  if(rewritten.getKind() == kind::CONST_BOOLEAN){
    pushBack(x);

    if(rewritten.getConst<bool>()){
      return true;
    }else{
      ++(d_statistics.d_conflicts);

      Node conf = flattenAnd(explainInternal(x));
      raiseConflict(conf);
      Debug("arith::congruenceManager") << "rewritten to false "<<x<<" with explanation "<< conf << std::endl;
      return false;
    }
  }

  Assert(rewritten.getKind() != kind::CONST_BOOLEAN);

  ConstraintP c = d_constraintDatabase.lookup(rewritten);
  if(c == NullConstraint){
    //using setup as there may not be a corresponding congruence literal yet
    d_setupLiteral(rewritten);
    c = d_constraintDatabase.lookup(rewritten);
    Assert(c != NullConstraint);
  }

  Debug("arith::congruenceManager")<< "x is "
                                   <<  c->hasProof() << " "
                                   << (x == rewritten) << " "
                                   << c->canBePropagated() << " "
                                   << c->negationHasProof() << std::endl;

  if(c->negationHasProof()){
    Node expC = explainInternal(x);
    ConstraintCP negC = c->getNegation();
    Node neg = negC->externalExplainByAssertions();
    Node conf = expC.andNode(neg);
    Node final = flattenAnd(conf);

    ++(d_statistics.d_conflicts);
    raiseConflict(final);
    Debug("arith::congruenceManager") << "congruenceManager found a conflict " << final << std::endl;
    return false;
  }

  // Cases for propagation
  // C : c has a proof
  // S : x == rewritten
  // P : c can be propagated
  //
  // CSP
  // 000 : propagate x, and mark C it as being explained
  // 001 : propagate x, and propagate c after marking it as being explained
  // 01* : propagate x, mark c but do not propagate c
  // 10* : propagate x, do not mark c and do not propagate c
  // 11* : drop the constraint, do not propagate x or c

  if(!c->hasProof() && x != rewritten){
    if(c->assertedToTheTheory()){
      pushBack(x, rewritten, c->getWitness());
    }else{
      pushBack(x, rewritten);
    }

    c->setEqualityEngineProof();
    if(c->canBePropagated() && !c->assertedToTheTheory()){

      ++(d_statistics.d_propagateConstraints);
      c->propagate();
    }
  }else if(!c->hasProof() && x == rewritten){
    if(c->assertedToTheTheory()){
      pushBack(x, c->getWitness());
    }else{
      pushBack(x);
    }
    c->setEqualityEngineProof();
  }else if(c->hasProof() && x != rewritten){
    if(c->assertedToTheTheory()){
      pushBack(x);
    }else{
      pushBack(x);
    }
  }else{
    Assert(c->hasProof() && x == rewritten);
  }
  return true;
}

void ArithCongruenceManager::explain(TNode literal, std::vector<TNode>& assumptions) {
  if (literal.getKind() != kind::NOT) {
    d_ee.explainEquality(literal[0], literal[1], true, assumptions);
  } else {
    d_ee.explainEquality(literal[0][0], literal[0][1], false, assumptions);
  }
}

void ArithCongruenceManager::enqueueIntoNB(const std::set<TNode> s, NodeBuilder<>& nb){
  std::set<TNode>::const_iterator it = s.begin();
  std::set<TNode>::const_iterator it_end = s.end();
  for(; it != it_end; ++it) {
    nb << *it;
  }
}

Node ArithCongruenceManager::explainInternal(TNode internal){
  std::vector<TNode> assumptions;
  explain(internal, assumptions);

  std::set<TNode> assumptionSet;
  assumptionSet.insert(assumptions.begin(), assumptions.end());

  if (assumptionSet.size() == 1) {
    // All the same, or just one
    return assumptions[0];
  }else{
    NodeBuilder<> conjunction(kind::AND);
    enqueueIntoNB(assumptionSet, conjunction);
    return conjunction;
  }
}

void ArithCongruenceManager::eqNotifyNewClass(TNode t) {
  if( d_eq_infer ){
    d_eq_infer->eqNotifyNewClass(t);
    fixpointInfer();
  }
}
void ArithCongruenceManager::eqNotifyPostMerge(TNode t1, TNode t2) {
  if( d_eq_infer ){
    d_eq_infer->eqNotifyMerge(t1, t2);
    fixpointInfer();
  }
}

Node ArithCongruenceManager::explain(TNode external){
  Trace("arith-ee") << "Ask for explanation of " << external << std::endl;
  Node internal = externalToInternal(external);
  Trace("arith-ee") << "...internal = " << internal << std::endl;
  return explainInternal(internal);
}

void ArithCongruenceManager::explain(TNode external, NodeBuilder<>& out){
  Node internal = externalToInternal(external);

  std::vector<TNode> assumptions;
  explain(internal, assumptions);
  std::set<TNode> assumptionSet;
  assumptionSet.insert(assumptions.begin(), assumptions.end());

  enqueueIntoNB(assumptionSet, out);
}

void ArithCongruenceManager::addWatchedPair(ArithVar s, TNode x, TNode y){
  Assert(!isWatchedVariable(s));

  Debug("arith::congruenceManager")
    << "addWatchedPair(" << s << ", " << x << ", " << y << ")" << std::endl;


  ++(d_statistics.d_watchedVariables);

  d_watchedVariables.add(s);

  Node eq = x.eqNode(y);
  d_watchedEqualities.set(s, eq);
}

void ArithCongruenceManager::assertionToEqualityEngine(bool isEquality, ArithVar s, TNode reason){
  Assert(isWatchedVariable(s));

  TNode eq = d_watchedEqualities[s];
  Assert(eq.getKind() == kind::EQUAL);

  Trace("arith-ee") << "Assert " << eq << ", pol " << isEquality << ", reason " << reason << std::endl;
  if(isEquality){
    d_ee.assertEquality(eq, true, reason);
  }else{
    d_ee.assertEquality(eq, false, reason);
  }
}

void ArithCongruenceManager::equalsConstant(ConstraintCP c){
  Assert(c->isEquality());

  ++(d_statistics.d_equalsConstantCalls);
  Debug("equalsConstant") << "equals constant " << c << std::endl;

  ArithVar x = c->getVariable();
  Node xAsNode = d_avariables.asNode(x);
  Node asRational = mkRationalNode(c->getValue().getNoninfinitesimalPart());


  //No guarentee this is in normal form!
  Node eq = xAsNode.eqNode(asRational);
  d_keepAlive.push_back(eq);

  Node reason = c->externalExplainByAssertions();
  d_keepAlive.push_back(reason);

  Trace("arith-ee") << "Assert equalsConstant " << eq << ", reason " << reason << std::endl;
  d_ee.assertEquality(eq, true, reason);
}

void ArithCongruenceManager::equalsConstant(ConstraintCP lb, ConstraintCP ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());

  ++(d_statistics.d_equalsConstantCalls);
  Debug("equalsConstant") << "equals constant " << lb << std::endl
                          << ub << std::endl;

  ArithVar x = lb->getVariable();
  Node reason = Constraint::externalExplainByAssertions(lb,ub);

  Node xAsNode = d_avariables.asNode(x);
  Node asRational = mkRationalNode(lb->getValue().getNoninfinitesimalPart());

  //No guarentee this is in normal form!
  Node eq = xAsNode.eqNode(asRational);
  d_keepAlive.push_back(eq);
  d_keepAlive.push_back(reason);

  Trace("arith-ee") << "Assert equalsConstant2 " << eq << ", reason " << reason << std::endl;
  d_ee.assertEquality(eq, true, reason);
}

void ArithCongruenceManager::addSharedTerm(Node x){
  d_ee.addTriggerTerm(x, THEORY_ARITH);
}

bool ArithCongruenceManager::fixpointInfer() {
  if( d_eq_infer ){
    while(! inConflict() && d_eqi_counter.get()<d_eq_infer->getNumPendingMerges() ) {
      Trace("snorm-infer-eq-debug") << "Processing " << d_eqi_counter.get() << " / " << d_eq_infer->getNumPendingMerges() << std::endl;
      Node eq = d_eq_infer->getPendingMerge( d_eqi_counter.get() );
      Trace("snorm-infer-eq") << "ArithCongruenceManager : Infer by normalization : " << eq << std::endl;
      if( !d_ee.areEqual( eq[0], eq[1] ) ){
        Node eq_exp = d_eq_infer->getPendingMergeExplanation( d_eqi_counter.get() );
        Trace("snorm-infer-eq") << "           explanation : " << eq_exp << std::endl;
        //regress explanation
        std::vector<TNode> assumptions;
        if( eq_exp.getKind()==kind::AND ){
          for( unsigned i=0; i<eq_exp.getNumChildren(); i++ ){
            explain( eq_exp[i], assumptions );
          }
        }else if( eq_exp.getKind()==kind::EQUAL ){
          explain( eq_exp, assumptions );
        }else{
          //eq_exp should be true
          Assert( eq_exp==d_true );
        }
        Node req_exp;
        if( assumptions.empty() ){
          req_exp = d_true;
        }else{
          std::set<TNode> assumptionSet;
          assumptionSet.insert(assumptions.begin(), assumptions.end());
          if( assumptionSet.size()==1 ){
            req_exp = assumptions[0];
          }else{
            NodeBuilder<> conjunction(kind::AND);
            enqueueIntoNB(assumptionSet, conjunction);
            req_exp = conjunction;
          }
        }
        Trace("snorm-infer-eq") << " regressed explanation : " << req_exp << std::endl;
        d_ee.assertEquality( eq, true, req_exp );
        d_keepAlive.push_back( req_exp );
      }else{
        Trace("snorm-infer-eq") << "...already equal." << std::endl;
      }
      d_eqi_counter = d_eqi_counter.get() + 1;
    }
  }
  return inConflict();
}



}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
