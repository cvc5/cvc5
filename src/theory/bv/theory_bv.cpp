/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: mdeters, lianah
 ** Minor contributors (to current version): barrett, ajreynol
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
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
    d_slicer(),
    d_bitblastSolver(c, this),
    d_coreSolver(c, this, &d_slicer),
    d_statistics(),
    d_conflict(c, false),
    d_literalsToPropagate(c),
    d_literalsToPropagateIndex(c, 0),
    d_propagatedBy(c)
  {}

TheoryBV::~TheoryBV() {}


void TheoryBV::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_coreSolver.setMasterEqualityEngine(eq);
}

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
  Debug("bitvector-preregister") << "TheoryBV::preRegister(" << node << ")" << std::endl;

  if (options::bitvectorEagerBitblast()) {
    // don't use the equality engine in the eager bit-blasting
    return;
  }

  if (node.getKind() == kind::EQUAL) {
    d_slicer.processEquality(node); 
  }
  
  d_bitblastSolver.preRegister(node);
  d_coreSolver.preRegister(node);
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
    Debug("bitvector-assertions") << "TheoryBV::check assertion " << fact << "\n";
  }

  if (!inConflict()) {
    // sending assertions to the equality solver first
    d_coreSolver.addAssertions(new_assertions, e);
  }

  // FIXME: this is not quite correct as it does not take into account cardinality constraints 

  //if (d_coreSolver.isCoreTheory()) {
    // paranoid check to make sure results of bit-blaster agree with slicer for core theory
    // if (inConflict()) {
    //   d_conflict = false;
    //   d_bitblastSolver.addAssertions(new_assertions, Theory::EFFORT_FULL); 
    //   Assert (inConflict()); 
    // } else {
    //   d_bitblastSolver.addAssertions(new_assertions, Theory::EFFORT_FULL); 
    //   Assert (!inConflict()); 
    // }
  //}
  //else {
  
  if (!inConflict() && !d_coreSolver.isCoreTheory()) {
    // sending assertions to the bitblast solver if it's not just core theory 
    d_bitblastSolver.addAssertions(new_assertions, e);
  }
  
  if (inConflict()) {
    sendConflict();
  }
}

void TheoryBV::collectModelInfo( TheoryModel* m, bool fullModel ){
  Assert(!inConflict());
  //  Assert (fullModel); // can only query full model
  d_coreSolver.collectModelInfo(m); 
  d_bitblastSolver.collectModelInfo(m); 
  
}

void TheoryBV::propagate(Effort e) {
  Debug("bitvector") << indent() << "TheoryBV::propagate()" << std::endl;

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
  
  if (t.getKind() == kind::EQUAL) {
    std::vector<Node> equalities;
    Slicer::splitEqualities(t, equalities);
    return utils::mkAnd(equalities); 
  }
  
  return t;
}

void TheoryBV::presolve() {
  Debug("bitvector") << "TheoryBV::presolve" << endl; 
  d_slicer.computeCoarsestBase(); 
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
  // Ask the appropriate subtheory for the explanation
  if (propagatedBy(literal, SUB_CORE)) {
    Debug("bitvector::explain") << "TheoryBV::explain(" << literal << "): CORE" << std::endl;
    d_coreSolver.explain(literal, assumptions);
  } else {
    Assert(propagatedBy(literal, SUB_BITBLAST));
    Debug("bitvector::explain") << "TheoryBV::explain(" << literal << ") : BITBLASTER" << std::endl;
    d_bitblastSolver.explain(literal, assumptions);
  }
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
    d_coreSolver.addSharedTerm(t);
  }
}



EqualityStatus TheoryBV::getEqualityStatus(TNode a, TNode b)
{
  if (options::bitvectorEagerBitblast()) {
    return EQUALITY_UNKNOWN;
  }

  EqualityStatus status = d_coreSolver.getEqualityStatus(a, b);
  if (status == EQUALITY_UNKNOWN) {
    status = d_bitblastSolver.getEqualityStatus(a, b);
  }

  return status;
}

