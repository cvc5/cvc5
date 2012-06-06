/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters
 ** Minor contributors (to current version): none
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

#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/valuation.h"
#include "theory/bv/bitblaster.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::context;

using namespace std;
using namespace CVC4::theory::bv::utils;




TheoryBV::TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo)
  : Theory(THEORY_BV, c, u, out, valuation, logicInfo),
    d_context(c),
    d_alreadyPropagatedSet(c),
    d_sharedTermsSet(c),
    d_bitblastSolver(c, this),
    d_equalitySolver(c, this),
    d_statistics(),
    d_conflict(c, false),
    d_literalsToPropagate(c),
    d_literalsToPropagateIndex(c, 0),
    d_propagatedBy(c)
  {}

TheoryBV::~TheoryBV() {}

TheoryBV::Statistics::Statistics():
  d_avgConflictSize("theory::bv::AvgBVConflictSize"),
  d_solveSubstitutions("theory::bv::NumberOfSolveSubstitutions", 0),
  d_solveTimer("theory::bv::solveTimer")
{
  StatisticsRegistry::registerStat(&d_avgConflictSize);
  StatisticsRegistry::registerStat(&d_solveSubstitutions);
  StatisticsRegistry::registerStat(&d_solveTimer); 
}

TheoryBV::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_avgConflictSize);
  StatisticsRegistry::unregisterStat(&d_solveSubstitutions);
  StatisticsRegistry::unregisterStat(&d_solveTimer); 
}

void TheoryBV::preRegisterTerm(TNode node) {
  BVDebug("bitvector-preregister") << "TheoryBV::preRegister(" << node << ")" << std::endl;

  if (Options::current()->bitvectorEagerBitblast) {
    // don't use the equality engine in the eager bit-blasting
    return;
  }

  d_bitblastSolver.preRegister(node);
  d_equalitySolver.preRegister(node); 
}

void TheoryBV::check(Effort e)
{
  BVDebug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;

  // if we are already in conflict just return the conflict 
  if (d_conflict) {
    BVDebug("bitvector") << indent() << "TheoryBV::check(): conflict " << d_conflictNode;
    d_out->conflict(d_conflictNode);
    d_statistics.d_avgConflictSize.addEntry(d_conflictNode.getNumChildren());
    return;
  }
  
  // getting the new assertions
  std::vector<TNode> new_assertions; 
  while (!done()) {
    Assertion assertion = get();
    TNode fact = assertion.assertion;
    new_assertions.push_back(fact);
    BVDebug("bitvector-assertions") << "TheoryBV::check assertion " << fact << "\n"; 
  }

  // sending assertions to the equality solver first
  bool ok = d_equalitySolver.addAssertions(new_assertions, e);
  
  if (ok) {
    // sending assertions to the bitblast solver
    ok = d_bitblastSolver.addAssertions(new_assertions, e); 
  }
  
  if (!ok) {
    // output conflict 
    Assert (d_conflict);
    BVDebug("bitvector") << indent() << "TheoryBV::check(): conflict " << d_conflictNode;
    d_out->conflict(d_conflictNode);
    d_statistics.d_avgConflictSize.addEntry(d_conflictNode.getNumChildren());
  }
}


Node TheoryBV::getValue(TNode n) {
  //NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    Unhandled(kind::VARIABLE);

  default:
    Unhandled(n.getKind());
  }
}


void TheoryBV::propagate(Effort e) {
  BVDebug("bitvector") << indent() << "TheoryBV::propagate()" << std::endl;

  if (d_conflict) {
    return;
  }

  // go through stored propagations
  for (; d_literalsToPropagateIndex < d_literalsToPropagate.size(); d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1) {
    TNode literal = d_literalsToPropagate[d_literalsToPropagateIndex];
    d_out->propagate(literal);
  }
}


Theory::PPAssertStatus TheoryBV::ppAssert(TNode in, SubstitutionMap& outSubstitutions) {
  switch(in.getKind()) {
  case kind::EQUAL:
    
    if (in[0].getMetaKind() == kind::metakind::VARIABLE && !in[1].hasSubterm(in[0])) {
      ++(d_statistics.d_solveSubstitutions); 
      outSubstitutions.addSubstitution(in[0], in[1]);
      return PP_ASSERT_STATUS_SOLVED;
    }
    if (in[1].getMetaKind() == kind::metakind::VARIABLE && !in[0].hasSubterm(in[1])) {
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


bool TheoryBV::storePropagation(TNode literal, SubTheory subtheory)
{
  Debug("bitvector") << indent() << "TheoryBV::storePropagation(" << literal  << ")" << std::endl;

  // If already in conflict, no more propagation
  if (d_conflict) {
    Debug("bitvector") << indent() << "TheoryBV::storePropagation(" << literal << "): already in conflict" << std::endl;
    return false;
  }

  // If propagated already, just skip
  PropagatedMap::const_iterator find = d_propagatedBy.find(literal);
  if (find != d_propagatedBy.end()) {
    return true;
  } else {
    d_propagatedBy[literal] = subtheory;
  }

  // See if the literal has been asserted already
  bool satValue = false;
  bool hasSatValue = d_valuation.hasSatValue(literal, satValue);

  // If asserted, we might be in conflict
  if (hasSatValue && !satValue) {
    Debug("bitvector-prop") << indent() << "TheoryBV::storePropagation(" << literal << ") => conflict" << std::endl;
    std::vector<TNode> assumptions;
    Node negatedLiteral = literal.getKind() == kind::NOT ? (Node) literal[0] : literal.notNode();
    assumptions.push_back(negatedLiteral);
    explain(literal, assumptions);
    setConflict(mkAnd(assumptions)); 
    return false;
  }

  // Nothing, just enqueue it for propagation and mark it as asserted already
  Debug("bitvector-prop") << indent() << "TheoryBV::storePropagation(" << literal << ") => enqueuing for propagation" << std::endl;
  d_literalsToPropagate.push_back(literal);

  // No conflict
  return true;
}/* TheoryBV::propagate(TNode) */


void TheoryBV::explain(TNode literal, std::vector<TNode>& assumptions) {
  // Ask the appropriate subtheory for the explanation 
  if (propagatedBy(literal, SUB_EQUALITY)) {
    BVDebug("bitvector::explain") << "TheoryBV::explain(" << literal << "): EQUALITY" << std::endl;
    d_equalitySolver.explain(literal, assumptions); 
  } else {
    Assert(propagatedBy(literal, SUB_BITBLAST));
    BVDebug("bitvector::explain") << "TheoryBV::explain(" << literal << ") : BITBLASTER" << std::endl;    
    d_bitblastSolver.explain(literal, assumptions); 
  }
}


Node TheoryBV::explain(TNode node) {
  BVDebug("bitvector::explain") << "TheoryBV::explain(" << node << ")" << std::endl;
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
  if (!Options::current()->bitvectorEagerBitblast && d_useEqualityEngine) {
    d_equalitySolver.addSharedTerm(t); 
  }
}


EqualityStatus TheoryBV::getEqualityStatus(TNode a, TNode b)
{
  if (Options::current()->bitvectorEagerBitblast) {
    return EQUALITY_UNKNOWN;
  }

  EqualityStatus status = d_equalitySolver.getEqualityStatus(a, b);
  if (status == EQUALITY_UNKNOWN) {
    status = d_bitblastSolver.getEqualityStatus(a, b);
  }

  return status;
}

