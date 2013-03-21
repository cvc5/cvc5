/*********************                                                        */
/*! \file bv_subtheory_eq.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): lianah
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "theory/bv/bv_subtheory_core.h"

#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/slicer.h"
#include "theory/model.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

CoreSolver::CoreSolver(context::Context* c, TheoryBV* bv)
  : SubtheorySolver(c, bv),
    d_notify(*this),
    d_equalityEngine(d_notify, c, "theory::bv::TheoryBV"),
    d_slicer(new Slicer(c, this)),
    d_isCoreTheory(c, true),
    d_reasons(c)
{
  if (d_useEqualityEngine) {

    // The kinds we are treating as function application in congruence
    d_equalityEngine.addFunctionKind(kind::BITVECTOR_CONCAT, true);
    //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_AND);
    //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_OR);
    //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_XOR);
    //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NOT);
    //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NAND);
    //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_NOR);
    //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_XNOR);
    //    d_equalityEngine.addFunctionKind(kind::BITVECTOR_COMP);
    d_equalityEngine.addFunctionKind(kind::BITVECTOR_MULT, true);
    d_equalityEngine.addFunctionKind(kind::BITVECTOR_PLUS, true);
    d_equalityEngine.addFunctionKind(kind::BITVECTOR_EXTRACT, true);
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

CoreSolver::~CoreSolver() {
  delete d_slicer; 
}
void CoreSolver::setMasterEqualityEngine(eq::EqualityEngine* eq) {
  d_equalityEngine.setMasterEqualityEngine(eq);
}

void CoreSolver::preRegister(TNode node) {
  if (!d_useEqualityEngine)
    return;

  if (node.getKind() == kind::EQUAL) {
      d_equalityEngine.addTriggerEquality(node);
      // d_slicer->processEquality(node);
  } else {
    d_equalityEngine.addTerm(node);
  }
}


void CoreSolver::explain(TNode literal, std::vector<TNode>& assumptions) {
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  }
}

Node CoreSolver::getBaseDecomposition(TNode a, std::vector<Node>& explanation) {
  std::vector<Node> a_decomp;
  d_slicer->getBaseDecomposition(a, a_decomp, explanation);
  Node new_a = utils::mkConcat(a_decomp);
  Debug("bv-slicer") << "CoreSolver::getBaseDecomposition " << a <<" => " << new_a << "\n"; 
  return new_a; 
}

bool CoreSolver::decomposeFact(TNode fact) {
  Debug("bv-slicer") << "CoreSolver::decomposeFact fact=" << fact << endl;  
  // assert decompositions since the equality engine does not know the semantics of
  // concat:
  //   a == a_1 concat ... concat a_k
  //   b == b_1 concat ... concat b_k

  if (fact.getKind() == kind::EQUAL) {
    TNode a = fact[0];
    TNode b = fact[1];

    d_slicer->processEquality(fact); 
    std::vector<Node> explanation; 
    Node new_a = getBaseDecomposition(a, explanation);
    Node new_b = getBaseDecomposition(b, explanation);

    explanation.push_back(fact);
    Node reason = utils::mkAnd(explanation); 
    d_reasons.insert(reason);
    
    Assert (utils::getSize(new_a) == utils::getSize(new_b) &&
            utils::getSize(new_a) == utils::getSize(a)); 
    // FIXME: do we still need to assert these? 
    NodeManager* nm = NodeManager::currentNM();
    Node a_eq_new_a = nm->mkNode(kind::EQUAL, a, new_a);
    Node b_eq_new_b = nm->mkNode(kind::EQUAL, b, new_b);

    d_reasons.insert(a_eq_new_a);
    d_reasons.insert(b_eq_new_b); 
    
    bool ok = true; 
    ok = assertFactToEqualityEngine(a_eq_new_a, utils::mkTrue());
    if (!ok) return false; 
    ok = assertFactToEqualityEngine(b_eq_new_b, utils::mkTrue());
    if (!ok) return false; 
    // assert the individual equalities as well
    //    a_i == b_i
    if (new_a.getKind() == kind::BITVECTOR_CONCAT &&
        new_b.getKind() == kind::BITVECTOR_CONCAT) {
      Assert (new_a.getNumChildren() == new_b.getNumChildren()); 
      for (unsigned i = 0; i < new_a.getNumChildren(); ++i) {
        Node eq_i = nm->mkNode(kind::EQUAL, new_a[i], new_b[i]);
        ok = assertFactToEqualityEngine(eq_i, reason);
        d_reasons.insert(eq_i); 
        if (!ok) return false;
      }
    }
    // merge the two terms in the slicer as well
    d_slicer->assertEquality(fact); 
  } else {
    // still need to register the terms
    d_slicer->processEquality(fact[0]);
    TNode a = fact[0][0];
    TNode b = fact[0][1];
    std::vector<Node> explanation_a; 
    Node new_a = getBaseDecomposition(a, explanation_a);
    Node reason_a = explanation_a.empty()? mkTrue() : mkAnd(explanation_a);
    assertFactToEqualityEngine(utils::mkNode(kind::EQUAL, a, new_a), reason_a);

    std::vector<Node> explanation_b; 
    Node new_b = getBaseDecomposition(b, explanation_b);
    Node reason_b = explanation_b.empty()? mkTrue() : mkAnd(explanation_b);
    assertFactToEqualityEngine(utils::mkNode(kind::EQUAL, b, new_b), reason_b);
    d_reasons.insert(reason_a);
    d_reasons.insert(reason_b); 
  }
  // finally assert the actual fact to the equality engine
  return assertFactToEqualityEngine(fact, fact);
}

bool CoreSolver::check(Theory::Effort e) {
  Trace("bitvector::core") << "CoreSolver::check \n";
  Assert (!d_bv->inConflict());

  bool ok = true; 
  std::vector<Node> core_eqs;
  while (! done()) {
    TNode fact = get(); 
    
    // update whether we are in the core fragment
    if (d_isCoreTheory && !d_slicer->isCoreTerm(fact)) {
      d_isCoreTheory = false; 
    }
    
    // only reason about equalities
    if (fact.getKind() == kind::EQUAL || (fact.getKind() == kind::NOT && fact[0].getKind() == kind::EQUAL)) {
      ok = decomposeFact(fact);
    } else {
      ok = assertFactToEqualityEngine(fact, fact); 
    }
    if (!ok)
      return false; 
  }
  
  // make sure to assert the new splits
  std::vector<Node> new_splits;
  d_slicer->getNewSplits(new_splits);
  for (unsigned i = 0; i < new_splits.size(); ++i) {
    ok = assertFactToEqualityEngine(new_splits[i], utils::mkTrue());
    if (!ok)
      return false; 
  }
  return true;
}

bool CoreSolver::assertFactToEqualityEngine(TNode fact, TNode reason) {
  // Notify the equality engine 
  if (d_useEqualityEngine && !d_bv->inConflict() && !d_bv->propagatedBy(fact, SUB_CORE) ) {
    Debug("bv-slicer-eq") << "CoreSolver::assertFactToEqualityEngine fact=" << fact << endl;
    // Debug("bv-slicer-eq") << "                     reason=" << reason << endl;
    bool negated = fact.getKind() == kind::NOT;
    TNode predicate = negated ? fact[0] : fact;
    if (predicate.getKind() == kind::EQUAL) {
      if (negated) {
        // dis-equality
        d_equalityEngine.assertEquality(predicate, false, reason);
      } else {
        // equality
        d_equalityEngine.assertEquality(predicate, true, reason);
      }
    } else {
      // Adding predicate if the congruence over it is turned on
      if (d_equalityEngine.isFunctionKind(predicate.getKind())) {
        d_equalityEngine.assertPredicate(predicate, !negated, reason);
      }
    }
  }

  // checking for a conflict
  if (d_bv->inConflict()) {
    return false;
  }  
  return true; 
}

bool CoreSolver::NotifyClass::eqNotifyTriggerEquality(TNode equality, bool value) {
  Debug("bitvector::core") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
  if (value) {
    return d_solver.storePropagation(equality);
  } else {
    return d_solver.storePropagation(equality.notNode());
  }
}

bool CoreSolver::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value) {
  Debug("bitvector::core") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false" ) << ")" << std::endl;
  if (value) {
    return d_solver.storePropagation(predicate);
  } else {
    return d_solver.storePropagation(predicate.notNode());
  }
}

bool CoreSolver::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
  Debug("bitvector::core") << "NotifyClass::eqNotifyTriggerTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
  if (value) {
    return d_solver.storePropagation(t1.eqNode(t2));
  } else {
    return d_solver.storePropagation(t1.eqNode(t2).notNode());
  }
}

void CoreSolver::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2) {
  d_solver.conflict(t1, t2);
}

bool CoreSolver::storePropagation(TNode literal) {
  return d_bv->storePropagation(literal, SUB_CORE);
}
  
void CoreSolver::conflict(TNode a, TNode b) {
  std::vector<TNode> assumptions;
  d_equalityEngine.explainEquality(a, b, true, assumptions);
  d_bv->setConflict(mkAnd(assumptions));
}

void CoreSolver::collectModelInfo(TheoryModel* m) {
  if (Debug.isOn("bitvector-model")) {
    context::CDQueue<Node>::const_iterator it = d_assertionQueue.begin();
    for (; it!= d_assertionQueue.end(); ++it) {
      Debug("bitvector-model") << "CoreSolver::collectModelInfo (assert "
                               << *it << ")\n";
    }
  }
  set<Node> termSet;
  d_bv->computeRelevantTerms(termSet);
  m->assertEqualityEngine(&d_equalityEngine, &termSet);
}
