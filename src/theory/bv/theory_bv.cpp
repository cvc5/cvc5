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

  Debug("bitvector") << "TheoryBV::preRegister(" << node << ")" << std::endl;

  if (node.getKind() == kind::EQUAL) {
    d_eqEngine.addTerm(node[0]);
    d_eqEngine.addTerm(node[1]);
    size_t triggerId = d_eqEngine.addTrigger(node[0], node[1]);
    Assert(triggerId == d_triggers.size());
    d_triggers.push_back(node);
  }
}

void TheoryBV::check(Effort e) {

  Debug("bitvector") << "TheoryBV::check(" << e << ")" << std::endl;

  while(!done()) {

    // Get the assertion
    TNode assertion = get();
    d_assertions.insert(assertion);

    Debug("bitvector") << "TheoryBV::check(" << e << "): asserting: " << assertion << std::endl;

    // Do the right stuff
    switch (assertion.getKind()) {
    case kind::EQUAL: {

      // Slice the equality
      std::vector<Node> lhsSlices, rhsSlices;
      d_sliceManager.addEquality(assertion[0], assertion[1], lhsSlices, rhsSlices);
      Assert(lhsSlices.size() == rhsSlices.size());

      // Add the equality to the equality engine
      for (int i = 0, i_end = lhsSlices.size(); i != i_end; ++ i) {
        bool ok = d_eqEngine.addEquality(lhsSlices[i], rhsSlices[i]);
        if (!ok) return;
      }
      break;
    }
    case kind::NOT: {
      // We need to check this as the equality trigger might have been true when we made it
      TNode equality = assertion[0];

      // No need to slice the equality, the whole thing *should* be deduced
      if (d_eqEngine.areEqual(equality[0], equality[1])) {
        vector<TNode> assertions;
        d_eqEngine.getExplanation(equality[0], equality[1], assertions);
        assertions.push_back(assertion);
        d_out->conflict(mkAnd(assertions));
        return;
      }
      break;
    }
    default:
      Unhandled();
    }
  }
}

bool TheoryBV::triggerEquality(size_t triggerId) {
  Debug("bitvector") << "TheoryBV::triggerEquality(" << triggerId << ")" << std::endl;
  Assert(triggerId < d_triggers.size());
  Debug("bitvector") << "TheoryBV::triggerEquality(" << triggerId << "): " << d_triggers[triggerId] << std::endl;

  TNode equality = d_triggers[triggerId];

  // If we have just asserted this equality ignore it
  if (d_assertions.contains(equality)) return true;

  // If we have a negation asserted, we have a confict
  if (d_assertions.contains(equality.notNode())) {

    vector<TNode> assertions;
    d_eqEngine.getExplanation(equality[0], equality[1], assertions);
    assertions.push_back(equality.notNode());
    d_out->conflict(mkAnd(assertions));

    return false;
  }

  // Otherwise we propagate this equality
  d_out->propagate(equality);

  return true;
}

Node TheoryBV::getValue(TNode n, Valuation* valuation) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( valuation->getValue(n[0]) == valuation->getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}
