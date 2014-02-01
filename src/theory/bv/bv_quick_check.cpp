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

prop::SatValue BVQuickCheck::checkSat(unsigned budget) {
  if (budget == 0) {
    bool ok = d_bitblaster->propagate();
    if (!ok) {
      //setConflict();
      return SAT_VALUE_FALSE;
    }
    return SAT_VALUE_UNKNOWN;
  }
  prop::SatValue res = d_bitblaster->solveWithBudget(budget);
  return res;
}

bool BVQuickCheck::addAssertion(TNode assertion) {
  Assert (assertion.getType().isBoolean());
  d_bitblaster->bbAtom(assertion);
  bool ok = d_bitblaster->assertToSat(assertion, false);
  return ok;
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

void BVQuickCheck::popToZero() {
  while (d_ctx->getLevel() > 0) {
    d_ctx->pop();
  }
}

BVQuickCheck::~BVQuickCheck() {
  delete d_bitblaster;
}

QuickXPlain::QuickXPlain()
  : d_solver(new BVQuickCheck())
  , d_statistics()
{}
QuickXPlain::~QuickXPlain() {
  delete d_solver;
}

void QuickXPlain::minimizeConflictInternal(unsigned low, unsigned high,
                                           std::vector<TNode>& conflict,
                                           std::vector<TNode>& new_conflict) {

  Assert (low <= high && high < conflict.size());
  
  if (low == high) {
    new_conflict.push_back(conflict[low]);
    return;
  }

  // check if top half is unsat
  unsigned new_low = (high - low + 1)/ 2 + low;
  d_solver->push();
  
  for (unsigned i = new_low; i <=high; ++i) {
    bool ok = d_solver->addAssertion(conflict[i]);
    if (!ok) {
      minimizeConflictInternal(new_low, i, conflict, new_conflict);
      return;
    }
  }

  SatValue res = d_solver->checkSat();
  d_solver->pop();
  
  Assert (res!= SAT_VALUE_UNKNOWN);
  // if unsat try to reduce it more
  if (res == SAT_VALUE_FALSE) {
    minimizeConflictInternal(new_low, high, conflict, new_conflict);
    return;
  }
  unsigned new_high = new_low - 1;
  d_solver->push();

  // check bottom half
  for (unsigned i = low; i <= new_high; ++i) {
    bool ok = d_solver->addAssertion(conflict[i]);
    if (!ok) {
      d_solver->pop();
      minimizeConflictInternal(low, i, conflict, new_conflict);
      return;
    }
  }
  res = d_solver->checkSat();
  Assert (res!= SAT_VALUE_UNKNOWN);
  
  if (res == SAT_VALUE_FALSE) {
    d_solver->pop();
    minimizeConflictInternal(low, new_high, conflict, new_conflict);
    return;
  }

  // conflict needs literals in both halves
  // keep bottom half in context (no pop)
  minimizeConflictInternal(new_low, high, conflict, new_conflict);
  d_solver->pop();
  d_solver->push();
  for (unsigned i = 0; i < new_conflict.size(); ++i) {
    d_solver->addAssertion(new_conflict[i]);
  }
  minimizeConflictInternal(low, new_high, conflict, new_conflict);
  d_solver->pop();
}

Node QuickXPlain::minimizeConflict(TNode confl) {
  TimerStat::CodeTimer xplainTimer(d_statistics.d_xplainTime);
  Assert (confl.getNumChildren() > 2);
  std::vector<TNode> conflict;
  for (unsigned i = 0; i < confl.getNumChildren(); ++i) {
    conflict.push_back(confl[i]);
  }
  d_solver->popToZero();
  std::vector<TNode> minimized;
  minimizeConflictInternal(0, conflict.size() - 1, conflict, minimized);
  return utils::mkAnd(minimized); 
}

QuickXPlain::Statistics::Statistics()
  : d_xplainTime("theory::bv::QuickXplainTime")
{
  StatisticsRegistry::registerStat(&d_xplainTime);
}

QuickXPlain::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_xplainTime);
}

