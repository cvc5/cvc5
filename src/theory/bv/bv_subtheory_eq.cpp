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

#include "theory/bv/bv_subtheory_eq.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/model.h"
using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

EqualitySolver::EqualitySolver(context::Context* c, TheoryBV* bv)
  : SubtheorySolver(c, bv),
    d_notify(*this),
    d_equalityEngine(d_notify, c, "theory::bv::TheoryBV")
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

void EqualitySolver::preRegister(TNode node) {
  if (!d_useEqualityEngine)
    return;

  if (node.getKind() == kind::EQUAL) {
      d_equalityEngine.addTriggerEquality(node);
  } else {
    d_equalityEngine.addTerm(node);
  }
}

void EqualitySolver::explain(TNode literal, std::vector<TNode>& assumptions) {
  bool polarity = literal.getKind() != kind::NOT;
  TNode atom = polarity ? literal : literal[0];
  if (atom.getKind() == kind::EQUAL) {
    d_equalityEngine.explainEquality(atom[0], atom[1], polarity, assumptions);
  } else {
    d_equalityEngine.explainPredicate(atom, polarity, assumptions);
  }
}

bool EqualitySolver::addAssertions(const std::vector<TNode>& assertions, Theory::Effort e) {
  BVDebug("bitvector::equality") << "EqualitySolver::addAssertions \n";
  Assert (!d_bv->inConflict());

  for (unsigned i = 0; i < assertions.size(); ++i) {
    TNode fact = assertions[i];

    // Notify the equality engine
    if (d_useEqualityEngine && !d_bv->inConflict() && !d_bv->propagatedBy(fact, SUB_EQUALITY) ) {
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
    if (d_bv->inConflict()) {
      return false;
    }
  }

  return true;
}

bool EqualitySolver::NotifyClass::eqNotifyTriggerEquality(TNode equality, bool value) {
  BVDebug("bitvector::equality") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
  if (value) {
    return d_solver.storePropagation(equality);
  } else {
    return d_solver.storePropagation(equality.notNode());
  }
}

bool EqualitySolver::NotifyClass::eqNotifyTriggerPredicate(TNode predicate, bool value) {
  BVDebug("bitvector::equality") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false" ) << ")" << std::endl;
  if (value) {
    return d_solver.storePropagation(predicate);
  } else {
    return d_solver.storePropagation(predicate.notNode());
  }
}

bool EqualitySolver::NotifyClass::eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value) {
  Debug("bitvector::equality") << "NotifyClass::eqNotifyTriggerTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
  if (value) {
    return d_solver.storePropagation(t1.eqNode(t2));
  } else {
    return d_solver.storePropagation(t1.eqNode(t2).notNode());
  }
}

void EqualitySolver::NotifyClass::eqNotifyConstantTermMerge(TNode t1, TNode t2) {
  d_solver.conflict(t1, t2);
}

bool EqualitySolver::storePropagation(TNode literal) {
  return d_bv->storePropagation(literal, SUB_EQUALITY);
}
  
void EqualitySolver::conflict(TNode a, TNode b) {
  std::vector<TNode> assumptions;
  d_equalityEngine.explainEquality(a, b, true, assumptions);
  d_bv->setConflict(mkAnd(assumptions));
}

void EqualitySolver::collectModelInfo(TheoryModel* m) {
  m->assertEqualityEngine(&d_equalityEngine);
}
