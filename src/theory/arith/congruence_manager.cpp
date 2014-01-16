/*********************                                                        */
/*! \file congruence_manager.cpp
 ** \verbatim
 ** Original author: Tim King
 ** Major contributors: none
 ** Minor contributors (to current version): Morgan Deters, Dejan Jovanovic
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

#include "theory/arith/congruence_manager.h"

#include "theory/arith/constraint.h"
#include "theory/arith/arith_utilities.h"

namespace CVC4 {
namespace theory {
namespace arith {

ArithCongruenceManager::ArithCongruenceManager(context::Context* c, ConstraintDatabase& cd, SetupLiteralCallBack setup, const ArithVariables& avars, RaiseConflict raiseConflict)
  : d_inConflict(c),
    d_raiseConflict(raiseConflict),
    d_notify(*this),
    d_keepAlive(c),
    d_propagatations(c),
    d_explanationMap(c),
    d_constraintDatabase(cd),
    d_setupLiteral(setup),
    d_avariables(avars),
    d_ee(d_notify, c, "theory::arith::ArithCongruenceManager")
{}

ArithCongruenceManager::Statistics::Statistics():
  d_watchedVariables("theory::arith::congruence::watchedVariables", 0),
  d_watchedVariableIsZero("theory::arith::congruence::watchedVariableIsZero", 0),
  d_watchedVariableIsNotZero("theory::arith::congruence::watchedVariableIsNotZero", 0),
  d_equalsConstantCalls("theory::arith::congruence::equalsConstantCalls", 0),
  d_propagations("theory::arith::congruence::propagations", 0),
  d_propagateConstraints("theory::arith::congruence::propagateConstraints", 0),
  d_conflicts("theory::arith::congruence::conflicts", 0)
{
  StatisticsRegistry::registerStat(&d_watchedVariables);
  StatisticsRegistry::registerStat(&d_watchedVariableIsZero);
  StatisticsRegistry::registerStat(&d_watchedVariableIsNotZero);
  StatisticsRegistry::registerStat(&d_equalsConstantCalls);
  StatisticsRegistry::registerStat(&d_propagations);
  StatisticsRegistry::registerStat(&d_propagateConstraints);
  StatisticsRegistry::registerStat(&d_conflicts);
}

ArithCongruenceManager::Statistics::~Statistics(){
  StatisticsRegistry::unregisterStat(&d_watchedVariables);
  StatisticsRegistry::unregisterStat(&d_watchedVariableIsZero);
  StatisticsRegistry::unregisterStat(&d_watchedVariableIsNotZero);
  StatisticsRegistry::unregisterStat(&d_equalsConstantCalls);
  StatisticsRegistry::unregisterStat(&d_propagations);
  StatisticsRegistry::unregisterStat(&d_propagateConstraints);
  StatisticsRegistry::unregisterStat(&d_conflicts);
}

void ArithCongruenceManager::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_ee.setMasterEqualityEngine(eq);
}

void ArithCongruenceManager::watchedVariableIsZero(Constraint lb, Constraint ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());
  Assert(lb->getValue().sgn() == 0);
  Assert(ub->getValue().sgn() == 0);

  ++(d_statistics.d_watchedVariableIsZero);

  ArithVar s = lb->getVariable();
  Node reason = ConstraintValue::explainConflict(lb,ub);

  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(true, s, reason);
}

void ArithCongruenceManager::watchedVariableIsZero(Constraint eq){
  Assert(eq->isEquality());
  Assert(eq->getValue().sgn() == 0);

  ++(d_statistics.d_watchedVariableIsZero);

  ArithVar s = eq->getVariable();

  //Explain for conflict is correct as these proofs are generated
  //and stored eagerly
  //These will be safe for propagation later as well
  Node reason = eq->explainForConflict();

  d_keepAlive.push_back(reason);
  assertionToEqualityEngine(true, s, reason);
}

void ArithCongruenceManager::watchedVariableCannotBeZero(Constraint c){
  ++(d_statistics.d_watchedVariableIsNotZero);

  ArithVar s = c->getVariable();

  //Explain for conflict is correct as these proofs are generated and stored eagerly
  //These will be safe for propagation later as well
  Node reason = c->explainForConflict();

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

  Constraint c = d_constraintDatabase.lookup(rewritten);
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
    Node neg = c->getNegation()->explainForConflict();
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
      pushBack(x, rewritten, c->getWitness());
    }else{
      pushBack(x, rewritten);
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
Node ArithCongruenceManager::explain(TNode external){
  Node internal = externalToInternal(external);
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

  if(isEquality){
    d_ee.assertEquality(eq, true, reason);
  }else{
    d_ee.assertEquality(eq, false, reason);
  }
}

void ArithCongruenceManager::equalsConstant(Constraint c){
  Assert(c->isEquality());

  ++(d_statistics.d_equalsConstantCalls);
  Debug("equalsConstant") << "equals constant " << c << std::endl;

  ArithVar x = c->getVariable();
  Node xAsNode = d_avariables.asNode(x);
  Node asRational = mkRationalNode(c->getValue().getNoninfinitesimalPart());


  //No guarentee this is in normal form!
  Node eq = xAsNode.eqNode(asRational);
  d_keepAlive.push_back(eq);

  Node reason = c->explainForConflict();
  d_keepAlive.push_back(reason);

  d_ee.assertEquality(eq, true, reason);
}

void ArithCongruenceManager::equalsConstant(Constraint lb, Constraint ub){
  Assert(lb->isLowerBound());
  Assert(ub->isUpperBound());
  Assert(lb->getVariable() == ub->getVariable());

  ++(d_statistics.d_equalsConstantCalls);
  Debug("equalsConstant") << "equals constant " << lb << std::endl
                          << ub << std::endl;

  ArithVar x = lb->getVariable();
  Node reason = ConstraintValue::explainConflict(lb,ub);

  Node xAsNode = d_avariables.asNode(x);
  Node asRational = mkRationalNode(lb->getValue().getNoninfinitesimalPart());

  //No guarentee this is in normal form!
  Node eq = xAsNode.eqNode(asRational);
  d_keepAlive.push_back(eq);
  d_keepAlive.push_back(reason);


  d_ee.assertEquality(eq, true, reason);
}

void ArithCongruenceManager::addSharedTerm(Node x){
  d_ee.addTriggerTerm(x, THEORY_ARITH);
}

}/* CVC4::theory::arith namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */
