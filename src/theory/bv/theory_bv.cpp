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


const bool d_useEqualityEngine = true;
const bool d_useSatPropagation = true;


TheoryBV::TheoryBV(context::Context* c, context::UserContext* u, OutputChannel& out, Valuation valuation, const LogicInfo& logicInfo)
  : Theory(THEORY_BV, c, u, out, valuation, logicInfo),
    d_context(c),
    d_assertions(c),
    d_bitblaster(new Bitblaster(c, this) ),
    d_bitblastQueue(c),
    d_alreadyPropagatedSet(c),
    d_sharedTermsSet(c),
    d_statistics(),
    d_notify(*this),
    d_equalityEngine(d_notify, c, "theory::bv::TheoryBV"),
    d_conflict(c, false),
    d_literalsToPropagate(c),
    d_literalsToPropagateIndex(c, 0),
    d_toBitBlast(c),
    d_propagatedBy(c)
  {
    if (d_useEqualityEngine) {

      // The kinds we are treating as function application in congruence
      d_equalityEngine.addFunctionKind(kind::BITVECTOR_CONCAT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_AND);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_OR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_XOR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NOT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NAND);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NOR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_XNOR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_COMP);
      d_equalityEngine.addFunctionKind(kind::BITVECTOR_MULT);
      d_equalityEngine.addFunctionKind(kind::BITVECTOR_PLUS);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SUB);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NEG);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_UDIV);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_UREM);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SDIV);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SREM);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SMOD);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SHL);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_LSHR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_ASHR);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_ULT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_ULE);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_UGT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_UGE);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SLT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SLE);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SGT);
      //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_SGE);

    }
  }

TheoryBV::~TheoryBV() {
  delete d_bitblaster; 
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
  BVDebug("bitvector-preregister") << "TheoryBV::preRegister(" << node << ")" << std::endl;

  if (Options::current()->bitvectorEagerBitblast) {
    // don't use the equality engine in the eager bit-blasting
    return;
  }

  if ((node.getKind() == kind::EQUAL ||
       node.getKind() == kind::BITVECTOR_ULT ||
       node.getKind() == kind::BITVECTOR_ULE ||
       node.getKind() == kind::BITVECTOR_SLT ||
       node.getKind() == kind::BITVECTOR_SLE) &&
      !d_bitblaster->hasBBAtom(node)) {
    d_bitblastQueue.push_back(node); 
  }

  if (d_useEqualityEngine) {
    switch (node.getKind()) {
      case kind::EQUAL:
        // Add the trigger for equality
        d_equalityEngine.addTriggerEquality(node);
        break;
      default:
        d_equalityEngine.addTerm(node);
        break;
    }
  }

}

void TheoryBV::check(Effort e)
{
  BVDebug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;

  if (Options::current()->bitvectorEagerBitblast) {
    while (!done()) {
      Assertion assertion = get();
      TNode fact = assertion.assertion;
      if (fact.getKind() == kind::NOT) {
        if (fact[0].getKind() != kind::BITVECTOR_BITOF) {
          d_bitblaster->bbAtom(fact[0]);
        }
      } else {
        if (fact.getKind() != kind::BITVECTOR_BITOF) {
          d_bitblaster->bbAtom(fact);
        }
      }
    }
    return;
  }

  // getting the new assertions
  
  std::vector<TNode> new_assertions; 
  while (!done() && !d_conflict) {
    Assertion assertion = get();
    TNode fact = assertion.assertion;
    new_assertions.push_back(fact);
    BVDebug("bitvector-assertions") << "TheoryBV::check assertion " << fact << "\n"; 
  }

  // sending assertions to equality engine first

  for (unsigned i = 0; i < new_assertions.size(); ++i) {
    TNode fact = new_assertions[i];
    TypeNode factType = fact[0].getType(); 

    // Notify the equality engine
    if (d_useEqualityEngine && !d_conflict && !propagatedBy(fact, SUB_EQUALITY) ) {
      bool negated = fact.getKind() == kind::NOT;
      TNode predicate = negated ? fact[0] : fact;
      if (predicate.getKind() == kind::EQUAL) {
        if (negated) {
          // dis-equality
          d_equalityEngine.assertEquality(predicate, false, fact);
        } else {
          // equality
          d_equalityEngine.assertEquality(predicate, true, fact);
        }
      } else {
        // Adding predicate if the congruence over it is turned on
        if (d_equalityEngine.isFunctionKind(predicate.getKind())) {
          d_equalityEngine.assertPredicate(predicate, !negated, fact);
        }
      }
    }

    // checking for a conflict 
    if (d_conflict) {
      BVDebug("bitvector") << indent() << "TheoryBV::check(): conflict " << d_conflictNode;
      d_out->conflict(d_conflictNode);
      return;
    }
  }

  // bit-blasting atoms on queue

  while (!d_bitblastQueue.empty()) {
    TNode node = d_bitblastQueue.front();
    d_bitblaster->bbAtom(node);
    d_bitblastQueue.pop(); 
  }
  
  // bit-blaster propagation 
  for (unsigned i = 0; i < new_assertions.size(); ++i) {
    TNode fact = new_assertions[i];
    if (!d_conflict && !propagatedBy(fact, SUB_BITBLASTER)) {
      // Some atoms have not been bit-blasted yet
      d_bitblaster->bbAtom(fact);
      // Assert to sat
      bool ok = d_bitblaster->assertToSat(fact, d_useSatPropagation);
      if (!ok) {
        std::vector<TNode> conflictAtoms;
        d_bitblaster->getConflict(conflictAtoms);
        d_statistics.d_avgConflictSize.addEntry(conflictAtoms.size());
        d_conflict = true;
        d_conflictNode = mkConjunction(conflictAtoms);
        break;
      }
    }
  }

  // If in conflict, output the conflict
  if (d_conflict) {
    BVDebug("bitvector") << indent() << "TheoryBV::check(): conflict " << d_conflictNode;
    d_out->conflict(d_conflictNode);
    return;
  }

  if (e == EFFORT_FULL || Options::current()->bitvectorEagerFullcheck) {
    Assert(done() && !d_conflict);
    BVDebug("bitvector") << "TheoryBV::check " << e << "\n";
    bool ok = d_bitblaster->solve();
    if (!ok) {
      std::vector<TNode> conflictAtoms;
      d_bitblaster->getConflict(conflictAtoms);
      d_statistics.d_avgConflictSize.addEntry(conflictAtoms.size());
      Node conflict = mkConjunction(conflictAtoms);
      d_out->conflict(conflict);
      BVDebug("bitvector") << "TheoryBV::check returns conflict: " <<conflict <<" \n ";
      return; 
    }
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
  for (; d_literalsToPropagateIndex < d_literalsToPropagate.size();
       d_literalsToPropagateIndex = d_literalsToPropagateIndex + 1)
  {
    TNode literal = d_literalsToPropagate[d_literalsToPropagateIndex];
    Node normalized = Rewriter::rewrite(literal);

    TNode atom = literal.getKind() == kind::NOT ? literal[0] : literal;  
    // check if it's a shared equality in the current context
    if (atom.getKind() != kind::EQUAL || d_valuation.isSatLiteral(normalized) ||
        (d_sharedTermsSet.find(atom[0]) != d_sharedTermsSet.end() &&
         d_sharedTermsSet.find(atom[1]) != d_sharedTermsSet.end())) {
    
      bool satValue;
      if (!d_valuation.hasSatValue(normalized, satValue) || satValue) {
        // check if we already propagated the negation
        Node negLiteral = literal.getKind() == kind::NOT ? (Node)literal[0] : mkNot(literal);
        if (d_alreadyPropagatedSet.find(negLiteral) != d_alreadyPropagatedSet.end()) {
          Debug("bitvector") << indent() << "TheoryBV::propagate(): in conflict " << literal << " and its negation both propagated \n"; 
          // we are in conflict
          std::vector<TNode> assumptions;
          explain(literal, assumptions);
          explain(negLiteral, assumptions);
          d_conflictNode = mkAnd(assumptions); 
          d_conflict = true;
          return;
        }
        
        BVDebug("bitvector") << indent() << "TheoryBV::propagate(): " << literal << std::endl;
        d_out->propagate(literal);
        d_alreadyPropagatedSet.insert(literal); 
      } else {
        Debug("bitvector") << indent() << "TheoryBV::propagate(): in conflict, normalized = " << normalized << std::endl;
        
        Node negatedLiteral;
        std::vector<TNode> assumptions;
        negatedLiteral = normalized.getKind() == kind::NOT ? (Node) normalized[0] : normalized.notNode();
        assumptions.push_back(negatedLiteral);
        explain(literal, assumptions);
        d_conflictNode = mkAnd(assumptions);
        d_conflict = true;
        return;
      }
    }
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
    d_conflictNode = mkAnd(assumptions);
    d_conflict = true;
    return false;
  }

  // Nothing, just enqueue it for propagation and mark it as asserted already
  Debug("bitvector-prop") << indent() << "TheoryBV::storePropagation(" << literal << ") => enqueuing for propagation" << std::endl;
  d_literalsToPropagate.push_back(literal);

  // No conflict
  return true;
}/* TheoryBV::propagate(TNode) */


void TheoryBV::explain(TNode literal, std::vector<TNode>& assumptions) {
  if (propagatedBy(literal, SUB_EQUALITY)) {
    bool polarity = literal.getKind() != kind::NOT;
    TNode atom = polarity ? literal : literal[0];
    if (atom.getKind() == kind::EQUAL) {
      d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
    } else {
      d_equalityEngine.explainPredicate(atom, polarity, assumptions);
    }
  } else {
    Assert(propagatedBy(literal, SUB_BITBLASTER));
    d_bitblaster->explain(literal, assumptions); 
  }
}


Node TheoryBV::explain(TNode node) {
  BVDebug("bitvector") << "TheoryBV::explain(" << node << ")" << std::endl;
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
    d_equalityEngine.addTriggerTerm(t);
  }
}


EqualityStatus TheoryBV::getEqualityStatus(TNode a, TNode b)
{
  if (Options::current()->bitvectorEagerBitblast) {
    return EQUALITY_UNKNOWN;
  }

  if (d_useEqualityEngine) {
    if (d_equalityEngine.areEqual(a, b)) {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    if (d_equalityEngine.areDisequal(a, b)) {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
  }
  return EQUALITY_UNKNOWN;
}

