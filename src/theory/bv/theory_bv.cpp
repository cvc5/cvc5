/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Original author: Dejan Jovanovic
 ** Major contributors: Morgan Deters, Liana Hadarean, lianah
 ** Minor contributors (to current version): Tim King, Andrew Reynolds, Clark Barrett
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

#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/slicer.h"
#include "theory/valuation.h"
#include "theory/bv/bitblaster.h"
#include "theory/bv/options.h"
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"
#include "theory/bv/bv_subtheory_core.h"
#include "theory/bv/bv_subtheory_inequality.h"
#include "theory/bv/bv_subtheory_bitblast.h"
#include "theory/model.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::context;

using namespace std;
using namespace CVC4::theory::bv::utils;

TheoryBV::TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo, QuantifiersEngine* qe)
  : Theory(THEORY_BV, c, u, out, valuation, logicInfo, qe),
    d_context(c),
    d_alreadyPropagatedSet(c),
    d_sharedTermsSet(c),
    d_subtheories(),
    d_subtheoryMap(),
    d_statistics(),
    d_conflict(c, false),
    d_literalsToPropagate(c),
    d_literalsToPropagateIndex(c, 0),
    d_propagatedBy(c)
  {
    SubtheorySolver* core_solver = new CoreSolver(c, this); 
    d_subtheories.push_back(core_solver);
    d_subtheoryMap[SUB_CORE] = core_solver;

    if (options::bitvectorInequalitySolver()) {
      SubtheorySolver* ineq_solver = new InequalitySolver(c, this); 
      d_subtheories.push_back(ineq_solver);
      d_subtheoryMap[SUB_INEQUALITY] = ineq_solver;
    }
    
    SubtheorySolver* bb_solver = new BitblastSolver(c, this); 
    d_subtheories.push_back(bb_solver);
    d_subtheoryMap[SUB_BITBLAST] = bb_solver;
  }

TheoryBV::~TheoryBV() {
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    delete d_subtheories[i]; 
  }
}

void TheoryBV::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  dynamic_cast<CoreSolver*>(d_subtheoryMap[SUB_CORE])->setMasterEqualityEngine(eq);
}

TheoryBV::Statistics::Statistics():
  d_avgConflictSize("theory::bv::AvgBVConflictSize"),
  d_solveSubstitutions("theory::bv::NumberOfSolveSubstitutions", 0),
  d_solveTimer("theory::bv::solveTimer"),
  d_numCallsToCheckFullEffort("theory::bv::NumberOfFullCheckCalls", 0),
  d_numCallsToCheckStandardEffort("theory::bv::NumberOfStandardCheckCalls", 0),
  d_weightComputationTimer("theory::bv::weightComputationTimer")
{
  StatisticsRegistry::registerStat(&d_avgConflictSize);
  StatisticsRegistry::registerStat(&d_solveSubstitutions);
  StatisticsRegistry::registerStat(&d_solveTimer);
  StatisticsRegistry::registerStat(&d_numCallsToCheckFullEffort);
  StatisticsRegistry::registerStat(&d_numCallsToCheckStandardEffort);
  StatisticsRegistry::registerStat(&d_weightComputationTimer);
}

TheoryBV::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_avgConflictSize);
  StatisticsRegistry::unregisterStat(&d_solveSubstitutions);
  StatisticsRegistry::unregisterStat(&d_solveTimer);
  StatisticsRegistry::unregisterStat(&d_numCallsToCheckFullEffort);
  StatisticsRegistry::unregisterStat(&d_numCallsToCheckStandardEffort);
  StatisticsRegistry::unregisterStat(&d_weightComputationTimer);
}



void TheoryBV::preRegisterTerm(TNode node) {
  Debug("bitvector-preregister") << "TheoryBV::preRegister(" << node << ")" << std::endl;

  if (options::bitvectorEagerBitblast()) {
    // don't use the equality engine in the eager bit-blasting
    d_subtheoryMap[SUB_BITBLAST]->preRegister(node);
    return;
  }
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    d_subtheories[i]->preRegister(node); 
  }
}

void TheoryBV::sendConflict() {
  Assert(d_conflict);
  if (d_conflictNode.isNull()) {
    return;
  } else {
    Debug("bitvector") << indent() << "TheoryBV::check(): conflict " << d_conflictNode;
    d_out->conflict(d_conflictNode);
    d_statistics.d_avgConflictSize.addEntry(d_conflictNode.getNumChildren());
    d_conflictNode = Node::null();
  }
}

void TheoryBV::check(Effort e)
{
  Debug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;
  if (options::bitvectorEagerBitblast()) {
    return;
  }

  if (Theory::fullEffort(e)) {
    ++(d_statistics.d_numCallsToCheckFullEffort); 
  } else {
    ++(d_statistics.d_numCallsToCheckStandardEffort); 
  }
  // if we are already in conflict just return the conflict
  if (inConflict()) {
    sendConflict();
    return;
  }

  while (!done()) {
    TNode fact = get().assertion;
    for (unsigned i = 0; i < d_subtheories.size(); ++i) {
      d_subtheories[i]->assertFact(fact); 
    }
  }

  bool ok = true;
  bool complete = false;
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    Assert (!inConflict()); 
    ok = d_subtheories[i]->check(e);
    complete = d_subtheories[i]->isComplete(); 

    if (!ok) {
      // if we are in a conflict no need to check with other theories
      Assert (inConflict());
      sendConflict();
      return; 
    }
    if (complete) {
      // if the last subtheory was complete we stop
      return; 
    }
  }
}

void TheoryBV::collectModelInfo( TheoryModel* m, bool fullModel ){
  Assert(!inConflict());
  //  Assert (fullModel); // can only query full model
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    if (d_subtheories[i]->isComplete()) {
      d_subtheories[i]->collectModelInfo(m);
      return; 
    }
  }
}

Node TheoryBV::getModelValue(TNode var) {
  Assert(!inConflict());
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    if (d_subtheories[i]->isComplete()) {
      return d_subtheories[i]->getModelValue(var); 
    }
  }
  Unreachable(); 
}

void TheoryBV::propagate(Effort e) {
  Debug("bitvector") << indent() << "TheoryBV::propagate()" << std::endl;

  if (options::bitvectorEagerBitblast()) {
    return;
  }

  if (inConflict()) {
    return;
  }

  // go through stored propagations
  bool ok = true;
  for (; d_literalsToPropagateIndex < d_literalsToPropagate.size() && ok; d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1) {
    TNode literal = d_literalsToPropagate[d_literalsToPropagateIndex];
    // temporary fix for incremental bit-blasting 
    if (d_valuation.isSatLiteral(literal)) {
      Debug("bitvector::propagate") << "TheoryBV:: propagating " << literal <<"\n";
      ok = d_out->propagate(literal);
    }
  }

  if (!ok) {
    Debug("bitvector::propagate") << indent() << "TheoryBV::propagate(): conflict from theory engine" << std::endl;
    setConflict();
  }
}


Theory::PPAssertStatus TheoryBV::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  switch(in.getKind()) {
  case kind::EQUAL:

    if (in[0].isVar() && !in[1].hasSubterm(in[0])) {
      ++(d_statistics.d_solveSubstitutions);
      outSubstitutions.addSubstitution(in[0], in[1]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[1].isVar() && !in[0].hasSubterm(in[1])) {
      ++(d_statistics.d_solveSubstitutions);
      outSubstitutions.addSubstitution(in[1], in[0]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    // to do constant propagations

    break;
  case kind::NOT:
    break;
  default:
    // TODO other predicates
    break;
  }
  return PP_ASSERT_STATUS_UNSOLVED;
}

Node TheoryBV::ppRewrite(TNode t)
{
  if (RewriteRule<BitwiseEq>::applies(t)) {
    Node result = RewriteRule<BitwiseEq>::run<false>(t);
    return Rewriter::rewrite(result);
  }

  if (options::bitvectorCoreSolver() && t.getKind() == kind::EQUAL) {
    std::vector<Node> equalities;
    Slicer::splitEqualities(t, equalities);
    return utils::mkAnd(equalities); 
  }
  
  return t;
}

void TheoryBV::presolve() {
  Debug("bitvector") << "TheoryBV::presolve" << endl; 
}

bool TheoryBV::storePropagation(TNode literal, SubTheory subtheory)
{
  Debug("bitvector::propagate") << indent() << getSatContext()->getLevel() << " " << "TheoryBV::storePropagation(" << literal << ", " << subtheory << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("bitvector::propagate") << indent() << "TheoryBV::storePropagation(" << literal << ", " << subtheory << "): already in conflict" << std::endl;
    return false;
  }

  // If propagated already, just skip
  PropagatedMap::const_iterator find = d_propagatedBy.find(literal);
  if (find != d_propagatedBy.end()) {
    return true;
  } else {
    bool polarity = literal.getKind() != kind::NOT;
    Node negatedLiteral = polarity ? literal.notNode() : (Node) literal[0];
    find = d_propagatedBy.find(negatedLiteral);
    if (find != d_propagatedBy.end() && (*find).second != subtheory) {
      // Safe to ignore this one, subtheory should produce a conflict
      return true;
    }
 
    d_propagatedBy[literal] = subtheory;
  }

  // Propagate differs depending on the subtheory
  // * bitblaster needs to be left alone until it's done, otherwise it doesn't know how to explain
  // * equality engine can propagate eagerly
  bool ok = true;
  if (subtheory == SUB_CORE) {
    d_out->propagate(literal);
    if (!ok) {
      setConflict();
    }
  } else {
    d_literalsToPropagate.push_back(literal);
  }
  return ok;

}/* TheoryBV::propagate(TNode) */


void TheoryBV::explain(TNode literal, std::vector<TNode>& assumptions) {
  Assert (wasPropagatedBySubtheory(literal));
  SubTheory sub = getPropagatingSubtheory(literal);
  d_subtheoryMap[sub]->explain(literal, assumptions);
}


Node TheoryBV::explain(TNode node) {
  Debug("bitvector::explain") << "TheoryBV::explain(" << node << ")" << std::endl;
  std::vector<TNode> assumptions;

  // Ask for the explanation
  explain(node, assumptions);
  // this means that it is something true at level 0
  if (assumptions.size() == 0) {
    return utils::mkTrue();
  }
  // return the explanation
  Node explanation = mkAnd(assumptions);
  Debug("bitvector::explain") << "TheoryBV::explain(" << node << ") => " << explanation << std::endl;
  return explanation;
}


void TheoryBV::addSharedTerm(TNode t) {
  Debug("bitvector::sharing") << indent() << "TheoryBV::addSharedTerm(" << t << ")" << std::endl;
  d_sharedTermsSet.insert(t);
  if (!options::bitvectorEagerBitblast() && d_useEqualityEngine) {
    for (unsigned i = 0; i < d_subtheories.size(); ++i) {
      d_subtheories[i]->addSharedTerm(t);
    }
  }
}


EqualityStatus TheoryBV::getEqualityStatus(TNode a, TNode b)
{
  if (options::bitvectorEagerBitblast()) {
    return EQUALITY_UNKNOWN;
  }
  
  for (unsigned i = 0; i < d_subtheories.size(); ++i) {
    EqualityStatus status = d_subtheories[i]->getEqualityStatus(a, b);
    if (status != EQUALITY_UNKNOWN) {
      return status; 
    }
  }
  return EQUALITY_UNKNOWN; ;
}

