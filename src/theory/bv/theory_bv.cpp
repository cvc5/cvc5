/*********************                                                        */
/*! \file theory_bv.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
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

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

using namespace std;

void TheoryBV::preRegisterTerm(TNode node) {

  BVDebug("bitvector") << "TheoryBV::preRegister(" << node << ")" << std::endl;

  if (node.getKind() == kind::EQUAL) {
    d_eqEngine.addTerm(node[0]);
    if (node[0].getKind() == kind::BITVECTOR_CONCAT) {
      for (unsigned i = 0, i_end = node[0].getNumChildren(); i < i_end; ++ i) {
        d_eqEngine.addTerm(node[0][i]);
      }
    }
    d_eqEngine.addTerm(node[1]);
    if (node[1].getKind() == kind::BITVECTOR_CONCAT) {
      for (unsigned i = 0, i_end = node[1].getNumChildren(); i < i_end; ++ i) {
        d_eqEngine.addTerm(node[1][i]);
      }
    }
    size_t triggerId = d_eqEngine.addTrigger(node[0], node[1]);
    Assert(triggerId == d_triggers.size());
    d_triggers.push_back(node);
  }
}

void TheoryBV::check(Effort e) {

  BVDebug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;

  // Get all the assertions
  std::vector<TNode> assertionsList;
  while (!done()) {
    // Get the assertion
    TNode assertion = get();
    d_assertions.insert(assertion);
    assertionsList.push_back(assertion);
  }

  for (unsigned i = 0; i < assertionsList.size(); ++ i) {

    TNode assertion = assertionsList[i];

    BVDebug("bitvector") << "TheoryBV::check(" << e << "): asserting: " << assertion << std::endl;

    // Do the right stuff
    switch (assertion.getKind()) {
    case kind::EQUAL: {
      // Slice and solve the equality
      bool ok = d_sliceManager.solveEquality(assertion[0], assertion[1]);
      if (!ok) return;
      break;
    }
    case kind::NOT: {
      // We need to check this as the equality trigger might have been true when we made it
      TNode equality = assertion[0];

      // Assumptions
      std::set<TNode> assumptions;
      Node lhsNormalized = d_eqEngine.normalize(equality[0], assumptions);
      Node rhsNormalized = d_eqEngine.normalize(equality[1], assumptions);

      BVDebug("bitvector") << "TheoryBV::check(" << e << "): normalizes to " << lhsNormalized << " = " << rhsNormalized << std::endl;
      
      // No need to slice the equality, the whole thing *should* be deduced
      if (lhsNormalized == rhsNormalized) {
        BVDebug("bitvector") << "TheoryBV::check(" << e << "): conflict with " << utils::setToString(assumptions) << std::endl;
        assumptions.insert(assertion);
        d_out->conflict(mkConjunction(assumptions));
        return;
      } else {
        d_disequalities.push_back(assertion);
      }
      break;
    }
    default:
      Unhandled();
    }
  }

  if (fullEffort(e)) {

    BVDebug("bitvector") << "TheoryBV::check(" << e << "): checking dis-equalities" << std::endl;

    for (unsigned i = 0, i_end = d_disequalities.size(); i < i_end; ++ i) {

      BVDebug("bitvector") << "TheoryBV::check(" << e << "): checking " << d_disequalities[i] << std::endl;

      TNode equality = d_disequalities[i][0];
      // Assumptions
      std::set<TNode> assumptions;
      Node lhsNormalized = d_eqEngine.normalize(equality[0], assumptions);
      Node rhsNormalized = d_eqEngine.normalize(equality[1], assumptions);

      BVDebug("bitvector") << "TheoryBV::check(" << e << "): normalizes to " << lhsNormalized << " = " << rhsNormalized << std::endl;

      // No need to slice the equality, the whole thing *should* be deduced
      if (lhsNormalized == rhsNormalized) {
        BVDebug("bitvector") << "TheoryBV::check(" << e << "): conflict with " << utils::setToString(assumptions) << std::endl;
        assumptions.insert(d_disequalities[i]);
        d_out->conflict(mkConjunction(assumptions));
        return;
      }
    }
  }
}

bool TheoryBV::triggerEquality(size_t triggerId) {
  BVDebug("bitvector") << "TheoryBV::triggerEquality(" << triggerId << ")" << std::endl;
  Assert(triggerId < d_triggers.size());
  BVDebug("bitvector") << "TheoryBV::triggerEquality(" << triggerId << "): " << d_triggers[triggerId] << std::endl;

  TNode equality = d_triggers[triggerId];

  // If we have just asserted this equality ignore it
  if (d_assertions.contains(equality)) return true;

  // If we have a negation asserted, we have a confict
  if (d_assertions.contains(equality.notNode())) {

    std::vector<TNode> explanation;
    d_eqEngine.getExplanation(equality[0], equality[1], explanation);
    std::set<TNode> assumptions;
    assumptions.insert(equality.notNode());
    utils::getConjuncts(explanation, assumptions);
    d_out->conflict(utils::mkConjunction(assumptions));

    return false;
  }

  // Otherwise we propagate this equality
  d_out->propagate(equality);

  return true;
}

Node TheoryBV::getValue(TNode n) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( d_valuation.getValue(n[0]) == d_valuation.getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}

void TheoryBV::explain(TNode node) {
  BVDebug("bitvector") << "TheoryBV::explain(" << node << ")" << std::endl;
  if(node.getKind() == kind::EQUAL) {
    std::vector<TNode> reasons;
    d_eqEngine.getExplanation(node[0], node[1], reasons);
    std::set<TNode> simpleReasons;
    utils::getConjuncts(reasons, simpleReasons);
    d_out->explanation(utils::mkConjunction(simpleReasons));
    return;
  }
  Unreachable();
}
