/*********************                                                        */
/*! \file bv_subtheory_bitblast.cpp
 ** \verbatim
 ** Original author: dejan
 ** Major contributors: none
 ** Minor contributors (to current version): lianah, mdeters
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009-2012  New York University and The University of Iowa
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "theory/bv/bv_subtheory_bitblast.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/bv/bitblaster.h"
#include "theory/bv/options.h"

using namespace std;
using namespace CVC4;
using namespace CVC4::context;
using namespace CVC4::theory;
using namespace CVC4::theory::bv;
using namespace CVC4::theory::bv::utils;

BitblastSolver::BitblastSolver(context::Context* c, TheoryBV* bv)
  : SubtheorySolver(c, bv),
    d_bitblaster(new Bitblaster(c, bv)),
    d_bitblastQueue(c),
    d_statistics()
{}

BitblastSolver::~BitblastSolver() {
  delete d_bitblaster;
}

BitblastSolver::Statistics::Statistics()
  : d_numCallstoCheck("theory::bv::BitblastSolver::NumCallsToCheck", 0)
{
  StatisticsRegistry::registerStat(&d_numCallstoCheck);
}
BitblastSolver::Statistics::~Statistics() {
  StatisticsRegistry::unregisterStat(&d_numCallstoCheck);
}

void BitblastSolver::preRegister(TNode node) {
  if ((node.getKind() == kind::EQUAL ||
       node.getKind() == kind::BITVECTOR_ULT ||
       node.getKind() == kind::BITVECTOR_ULE ||
       node.getKind() == kind::BITVECTOR_SLT ||
       node.getKind() == kind::BITVECTOR_SLE) &&
      !d_bitblaster->hasBBAtom(node)) {
    d_bitblastQueue.push_back(node);
  }
}

void BitblastSolver::explain(TNode literal, std::vector<TNode>& assumptions) {
  d_bitblaster->explain(literal, assumptions);
}


bool BitblastSolver::check(Theory::Effort e) {
  Debug("bv-bitblast") << "BitblastSolver::check (" << e << ")\n"; 
  ++(d_statistics.d_numCallstoCheck); 
  //// Eager bit-blasting
  if (options::bitvectorEagerBitblast()) {
    while (!done()) {
      TNode assertion = get(); 
      TNode atom = assertion.getKind() == kind::NOT ? assertion[0] : assertion;
      if (atom.getKind() != kind::BITVECTOR_BITOF) {
        d_bitblaster->bbAtom(atom);
      }
      return true;
    }
  }

  //// Lazy bit-blasting
  // bit-blast enqueued nodes
  while (!d_bitblastQueue.empty()) {
    TNode atom = d_bitblastQueue.front();
    d_bitblaster->bbAtom(atom);
    d_bitblastQueue.pop();
  }

  // Processing assertions  
  while (!done()) {
    TNode fact = get();
    Debug("bv-bitblast") << "  fact " << fact << ")\n"; 
    if (!d_bv->inConflict() && (!d_bv->wasPropagatedBySubtheory(fact) || d_bv->getPropagatingSubtheory(fact) != SUB_BITBLAST)) {
      // Some atoms have not been bit-blasted yet
      d_bitblaster->bbAtom(fact);
      // Assert to sat
      bool ok = d_bitblaster->assertToSat(fact, d_useSatPropagation);
      if (!ok) {
        std::vector<TNode> conflictAtoms;
        d_bitblaster->getConflict(conflictAtoms);
        d_bv->setConflict(mkConjunction(conflictAtoms));
        return false;
      }
    }
  }

  // We need to ensure we are fully propagated, so propagate now
  if (d_useSatPropagation) {
    bool ok = d_bitblaster->propagate();
    if (!ok) {
      std::vector<TNode> conflictAtoms;
      d_bitblaster->getConflict(conflictAtoms);
      d_bv->setConflict(mkConjunction(conflictAtoms));
      return false;
    }
  }

  // Solving
  if (e == Theory::EFFORT_FULL || options::bitvectorEagerFullcheck()) {
    Assert(!d_bv->inConflict());
    Debug("bitvector::bitblaster") << "BitblastSolver::addAssertions solving. \n";
    bool ok = d_bitblaster->solve();
    if (!ok) {
      std::vector<TNode> conflictAtoms;
      d_bitblaster->getConflict(conflictAtoms);
      Node conflict = mkConjunction(conflictAtoms);
      d_bv->setConflict(conflict);
      return false;
    }
  }

  return true;
}

EqualityStatus BitblastSolver::getEqualityStatus(TNode a, TNode b) {
  return d_bitblaster->getEqualityStatus(a, b);
}

void BitblastSolver::collectModelInfo(TheoryModel* m) {
  return d_bitblaster->collectModelInfo(m); 
}

Node BitblastSolver::getModelValue(TNode node) {
  Node val = d_bitblaster->getVarValue(node);
  Assert (val != Node() || d_bv->isSharedTerm(node));
  return val; 
}
