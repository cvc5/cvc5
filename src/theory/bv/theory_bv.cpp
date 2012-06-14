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
#include "theory/bv/theory_bv_rewrite_rules_normalization.h"

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

void TheoryBV::sendConflict() {
  Assert(d_conflict);
  if (d_conflictNode.isNull()) {
    return;
  } else {
    BVDebug("bitvector") << indent() << "TheoryBV::check(): conflict " << d_conflictNode;
    d_out->conflict(d_conflictNode);
    d_statistics.d_avgConflictSize.addEntry(d_conflictNode.getNumChildren());
    d_conflictNode = Node::null();
  }
}

void TheoryBV::check(Effort e)
{
  BVDebug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;

  // if we are already in conflict just return the conflict 
  if (inConflict()) {
    sendConflict();
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

  if (!inConflict()) {
    // sending assertions to the equality solver first
    d_equalitySolver.addAssertions(new_assertions, e);
  }
  
  if (!inConflict()) {
    // sending assertions to the bitblast solver
    d_bitblastSolver.addAssertions(new_assertions, e);
  }
  
  if (inConflict()) {
    sendConflict();
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

  if (inConflict()) {
    return;
  }

  // go through stored propagations
  bool ok = true;
  for (; d_literalsToPropagateIndex < d_literalsToPropagate.size() && ok; d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1) {
    TNode literal = d_literalsToPropagate[d_literalsToPropagateIndex];
    ok = d_out->propagate(literal);
  }

  if (!ok) {
    BVDebug("bitvector::propagate") << indent() << "TheoryBV::propagate(): conflict from theory engine" << std::endl;
    setConflict();
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


Node TheoryBV::ppRewrite(TNode t)
{
  if (RewriteRule<BitwiseEq>::applies(t)) {
    Node result = RewriteRule<BitwiseEq>::run<false>(t);
    return Rewriter::rewrite(result);
  }
  return t;
}


bool TheoryBV::storePropagation(TNode literal, SubTheory subtheory)
{
  Debug("bitvector::propagate") << indent() << "TheoryBV::storePropagation(" << literal << ", " << subtheory << ")" << std::endl;

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
  if (subtheory == SUB_EQUALITY) {
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

