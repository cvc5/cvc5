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
#include "theory/bv/theory_bv_rewrite_rules.h"

#include "theory/theory_engine.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

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

RewriteResponse TheoryBV::postRewrite(TNode node, bool topLevel) {

  Debug("bitvector") << "TheoryBV::postRewrite(" << node << ", topLevel = " << (topLevel? "true" : "false") << ")" << std::endl;

  Node result;

  if (node.getKind() == kind::CONST_BITVECTOR /* || isLeaf(n)) */)
    result = node;
  else {
    switch (node.getKind()) {
    case kind::BITVECTOR_CONCAT:
      result = LinearRewriteStrategy<
                  // Flatten the top level concatenations
                  CoreRewriteRules::ConcatFlatten,
                  // Merge the adjacent extracts on non-constants
                  CoreRewriteRules::ConcatExtractMerge,
                  // Merge the adjacent extracts on constants
                  CoreRewriteRules::ConcatConstantMerge,
                  // At this point only Extract-Whole could apply, if the result is only one extract
                  // or at some sub-expression if the result is a concatenation.
                  ApplyRuleToChildren<kind::BITVECTOR_CONCAT, CoreRewriteRules::ExtractWhole>
               >::apply(node);
      break;
    case kind::BITVECTOR_EXTRACT:
      result = LinearRewriteStrategy<
                  // Extract over a constant gives a constant
                  CoreRewriteRules::ExtractConstant,
                  // Extract over an extract is simplified to one extract
                  CoreRewriteRules::ExtractExtract,
                  // Extract over a concatenation is distributed to the appropriate concatenations
                  CoreRewriteRules::ExtractConcat,
                  // At this point only Extract-Whole could apply
                  CoreRewriteRules::ExtractWhole
                >::apply(node);
      break;
    case kind::EQUAL:
      result = LinearRewriteStrategy<
                  // Two distinct values rewrite to false
                  CoreRewriteRules::FailEq,
                  // If both sides are equal equality is true
                  CoreRewriteRules::SimplifyEq
                >::apply(node);
      break;
    default:
      // TODO: figure out when this is an operator
      result = node;
      break;
      // Unhandled();
    }
  }

  Debug("bitvector") << "TheoryBV::postRewrite(" << node << ", topLevel = " << (topLevel? "true" : "false") << ") => " << result << std::endl;

  return RewriteComplete(result);
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
      bool ok = d_eqEngine.addEquality(assertion[0], assertion[1]);
      if (!ok) return;
      break;
    }
    case kind::NOT: {
      // We need to check this as the equality trigger might have been true when we made it
      TNode equality = assertion[0];
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

Node TheoryBV::getValue(TNode n, TheoryEngine* engine) {
  NodeManager* nodeManager = NodeManager::currentNM();

  switch(n.getKind()) {

  case kind::VARIABLE:
    Unhandled(kind::VARIABLE);

  case kind::EQUAL: // 2 args
    return nodeManager->
      mkConst( engine->getValue(n[0]) == engine->getValue(n[1]) );

  default:
    Unhandled(n.getKind());
  }
}
