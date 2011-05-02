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

    d_normalization[node] = new Normalization(d_context, node);
  }
}

void TheoryBV::check(Effort e) {

  BVDebug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;

  // Normalization iterators
  NormalizationMap::iterator it = d_normalization.begin();
  NormalizationMap::iterator it_end = d_normalization.end();

  // Get all the assertions
  std::vector<TNode> assertionsList;
  while (!done()) {
    // Get the assertion
    TNode assertion = get();
    d_assertions.insert(assertion);
    assertionsList.push_back(assertion);
  }

  bool normalizeEqualities = false;

  for (unsigned i = 0; i < assertionsList.size(); ++ i) {

    TNode assertion = assertionsList[i];

    BVDebug("bitvector") << "TheoryBV::check(" << e << "): asserting: " << assertion << std::endl;

    // Do the right stuff
    switch (assertion.getKind()) {
    case kind::EQUAL: {
      // Slice and solve the equality
      bool ok = d_sliceManager.solveEquality(assertion[0], assertion[1]);
      if (!ok) return;
      // Normalize all equalities
      normalizeEqualities = true;
      it = d_normalization.begin();
      it = d_normalization.end();
      break;
    }
    case kind::NOT: {
      if (!normalizeEqualities) {
        // We still need to check this dis-equality, as it might have been pre-registered just now
        // so we didn't have a chance to propagate
        it = d_normalization.find(assertion[0]);
        if (it->second->assumptions.size() == 1) {
          // Just normalize this equality
          normalizeEqualities = true;
          it_end = it;
          it_end ++;
        }
      }
      break;
    }
    default:
      Unhandled(assertion.getKind());
    }
  }

  if (normalizeEqualities) {

    BVDebug("bitvector") << "Checking for propagations" << std::endl;
  
    NormalizationMap::iterator it = d_normalization.begin();
    NormalizationMap::iterator it_end = d_normalization.end();
    for(; it != it_end; ++ it) {

      TNode equality = it->first;
      BVDebug("bitvector") << "Checking " << equality << std::endl;
      Normalization& normalization = *it->second;
      
      // If asserted, we don't care
      if (d_assertions.find(equality) != d_assertions.end()) continue; 

      // Assumptions
      std::set<TNode> assumptions; 
      TNode lhs = normalization.equalities.back()[0];
      TNode rhs = normalization.equalities.back()[1];
      // If already satisfied, do nothing
      if (lhs == rhs) continue;

      Node lhsNormalized = d_eqEngine.normalize(lhs, assumptions);
      Node rhsNormalized = d_eqEngine.normalize(rhs, assumptions);

      if (lhsNormalized == lhs && rhsNormalized == rhs) continue;

      normalization.equalities.push_back(lhsNormalized.eqNode(rhsNormalized));
      normalization.assumptions.push_back(assumptions);

      BVDebug("bitvector") << "Adding normalization " << lhsNormalized.eqNode(rhsNormalized) << std::endl;
      BVDebug("bitvector") << "       assumptions   " << setToString(assumptions) << std::endl;


      BVDebug("bitvector") << "TheoryBV::check(" << e << "): normalizes to " << lhsNormalized << " = " << rhsNormalized << std::endl;

      // If both are equal we can propagate
      bool propagate = lhsNormalized == rhsNormalized;
      // otherwise if both are constants, we propagate negation (if not already there)
      bool propagateNegation = !propagate &&
          lhsNormalized.getKind() == kind::CONST_BITVECTOR && rhsNormalized.getKind() == kind::CONST_BITVECTOR
          && d_assertions.find(equality.notNode()) == d_assertions.end();
          ;
      if (propagate || propagateNegation) {
        Node implied = propagate        ? Node(equality)     : equality.notNode() ;
        Node impliedNegated = propagate ? equality.notNode() : Node(equality)     ;
        // If the negation of what's implied has been asserted, we are in conflict
        if (d_assertions.find(impliedNegated) != d_assertions.end()) {
          BVDebug("bitvector") << "TheoryBV::check(" << e << "): conflict with " << utils::setToString(assumptions) << std::endl;
          // Construct the assumptions
          for (unsigned i = 0; i < normalization.assumptions.size(); ++ i) {
            assumptions.insert(normalization.assumptions[i].begin(), normalization.assumptions[i].end());
          }
          // Make the conflict
          assumptions.insert(impliedNegated);
          d_out->conflict(mkConjunction(assumptions));
          return;
        }
        // Otherwise we propagate the implication
        else {
          BVDebug("bitvector") << "TheoryBV::check(" << e << "): propagating " << implied << std::endl;
          d_out->propagate(implied);
          d_assertions.insert(implied);
        }
      }
    }
  }
}

bool TheoryBV::triggerEquality(size_t triggerId) {
  BVDebug("bitvector") << "TheoryBV::triggerEquality(" << triggerId << ")" << std::endl;
  Assert(triggerId < d_triggers.size());
  BVDebug("bitvector") << "TheoryBV::triggerEquality(" << triggerId << "): " << d_triggers[triggerId] << std::endl;

  return true;

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

  TNode equality = node.getKind() == kind::NOT ? node[0] : node;
  Assert(equality.getKind() == kind::EQUAL);

  context::CDList< set<TNode> >& vec = d_normalization[equality]->assumptions;
  std::set<TNode> assumptions;
  for (unsigned i = 0; i < vec.size(); ++ i) {
    BVDebug("bitvector") << "Adding normalization " << d_normalization[equality]->equalities[i] << std::endl;
    BVDebug("bitvector") << "       assumptions   " << setToString(d_normalization[equality]->assumptions[i]) << std::endl;
    assumptions.insert(vec[i].begin(), vec[i].end());
  }
  d_out->explanation(utils::mkConjunction(assumptions));
  return;
}
