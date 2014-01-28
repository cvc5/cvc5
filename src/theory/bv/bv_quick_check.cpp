/*********************                                                        */
/*! \file bv_quick_check.cpp
 ** \verbatim
 ** Original author: Liana Hadaren
 ** Major contributors: none
 ** Minor contributors (to current version): none
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2013  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Wrapper around the SAT solver used for bitblasting.
 **
 ** Wrapper around the SAT solver used for bitblasting.
 **/

#include "theory/bv/bv_quick_check.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;


BVQuickCheck::BVQuickCheck()
  : d_ctx(new context::Context())
  , d_bitblaster(d_ctx)
{}

Node BVQuickCheck::constructConflict() {
  std::vector<TNode> conflict;
  d_bitblaster->getConflict(conflict);
  return utils::mkConjunction(conflict); 
}
// TODO: return enum 
prop::SatValue BVQuickCheck::checkSat(std::vector<TNode>& assumptions, bool propagation_only) {
  Node conflict; 
  push(); 
  for (unsigned i = 0; i < assumptions.size(); ++i) {
    TNode a = assumptions[i];
    Assert (a.getType().isBoolean());
    d_bitblaster->bbAtom(a[i]);
    bool ok = d_bitblaster->assertToSat(a, false);
    if (!ok) {
      conflict = constructConflict(); 
      pop();
      return conflict; 
    }
  }

  if (propagation_only) {
    bool ok = d_bitblaster->propagate();
    if (!ok) {
      conflict = constructConflict();
    }
    pop();
    return conflict; 
  }

  bool ok = d_bitblaster->solve();
  if (!ok) {
    conflict = constructConflict();
  }
  pop();
  return conflict; 
}


void BVQuickCheck::push() {
  d_ctx->push();
}

void BVQuickCheck::pop() {
  d_ctx->pop();
}
/** 
 * Constructs a new sat solver which requires throwing out the atomBBCache
 * but keeps all the termBBCache
 * 
 */
void BVQuickCheck::reset() {
  d_bitblaster->clearSolver(); 
}
