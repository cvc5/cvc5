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
#include "theory/bv/theory_bv_utils.h"

#include "theory/bv/bitblaster_template.h"

using namespace CVC4;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::prop;

BVQuickCheck::BVQuickCheck()
  : d_ctx(new context::Context())
  , d_bitblaster(new TLazyBitblaster(d_ctx, NULL, "algebraic"))
  , d_conflict()
  , d_inConflict(d_ctx, false)
{}


bool BVQuickCheck::inConflict() { return d_inConflict.get(); }

uint64_t BVQuickCheck::computeAtomWeight(TNode node, NodeSet& seen) {
  return d_bitblaster->computeAtomWeight(node, seen);
}

void BVQuickCheck::setConflict() {
  Assert (!inConflict());
  std::vector<TNode> conflict;
  d_bitblaster->getConflict(conflict);
  Node confl = utils::mkConjunction(conflict);
  d_inConflict = true;
  d_conflict = confl;
}

prop::SatValue BVQuickCheck::checkSat(std::vector<Node>& assumptions, unsigned long budget) {
  Node conflict; 

  for (unsigned i = 0; i < assumptions.size(); ++i) {
    TNode a = assumptions[i];
    Assert (a.getType().isBoolean());
    d_bitblaster->bbAtom(a);
    bool ok = d_bitblaster->assertToSat(a, false);
    if (!ok) {
      setConflict(); 
      return SAT_VALUE_FALSE; 
    }
  }
  
  if (budget == 0) {
    bool ok = d_bitblaster->propagate();
    if (!ok) {
      setConflict();
      return SAT_VALUE_FALSE;
    }
    // TODO: could be SAT - check assignment is full
    return SAT_VALUE_UNKNOWN;
  }

  prop::SatValue res = d_bitblaster->solveWithBudget(budget);
  if (res == SAT_VALUE_FALSE) {
    setConflict();
    return res;
  }
  // could be unknown or could be sat
   return res;
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
  // while (d_ctx->getLevel() > 0) {
  //   d_ctx->pop();
  // }
  d_bitblaster->clearSolver(); 
}

BVQuickCheck::~BVQuickCheck() {
  delete d_bitblaster;
}
