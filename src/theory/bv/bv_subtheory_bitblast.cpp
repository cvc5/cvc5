/*********************                                                        */
/*! \file bv_subtheory_bitblast.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Aina Niemetz, Dejan Jovanovic
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#include "theory/bv/bv_subtheory_bitblast.h"
#include "decision/decision_attributes.h"
#include "options/bv_options.h"
#include "options/decision_options.h"
#include "smt/smt_statistics_registry.h"
#include "theory/bv/abstraction.h"
#include "theory/bv/bitblast/lazy_bitblaster.h"
#include "theory/bv/bv_quick_check.h"
#include "theory/bv/theory_bv.h"
#include "theory/bv/theory_bv_utils.h"

using namespace std;
using namespace CVC4::context;

namespace CVC4 {
namespace theory {
namespace bv {

BitblastSolver::BitblastSolver(context::Context* c, TheoryBV* bv)
    : SubtheorySolver(c, bv),
      d_bitblaster(new TLazyBitblaster(c, bv, "theory::bv::lazy")),
      d_bitblastQueue(c),
      d_statistics(),
      d_validModelCache(c, true),
      d_lemmaAtomsQueue(c),
      d_useSatPropagation(options::bitvectorPropagate()),
      d_abstractionModule(NULL),
      d_quickCheck(),
      d_quickXplain()
{
  if (options::bitvectorQuickXplain())
  {
    d_quickCheck.reset(new BVQuickCheck("bb", bv));
    d_quickXplain.reset(new QuickXPlain("bb", d_quickCheck.get()));
  }
}

BitblastSolver::~BitblastSolver() {}

BitblastSolver::Statistics::Statistics()
  : d_numCallstoCheck("theory::bv::BitblastSolver::NumCallsToCheck", 0)
  , d_numBBLemmas("theory::bv::BitblastSolver::NumTimesLemmasBB", 0)
{
  smtStatisticsRegistry()->registerStat(&d_numCallstoCheck);
  smtStatisticsRegistry()->registerStat(&d_numBBLemmas);
}
BitblastSolver::Statistics::~Statistics() {
  smtStatisticsRegistry()->unregisterStat(&d_numCallstoCheck);
  smtStatisticsRegistry()->unregisterStat(&d_numBBLemmas);
}

void BitblastSolver::setAbstraction(AbstractionModule* abs) {
  d_abstractionModule = abs;
  d_bitblaster->setAbstraction(abs);
}

void BitblastSolver::preRegister(TNode node) {
  if ((node.getKind() == kind::EQUAL ||
       node.getKind() == kind::BITVECTOR_ULT ||
       node.getKind() == kind::BITVECTOR_ULE ||
       node.getKind() == kind::BITVECTOR_SLT ||
       node.getKind() == kind::BITVECTOR_SLE) &&
      !d_bitblaster->hasBBAtom(node)) {
    CodeTimer weightComputationTime(d_bv->d_statistics.d_weightComputationTimer);
    d_bitblastQueue.push_back(node);
    if ((options::decisionUseWeight() || options::decisionThreshold() != 0) &&
        !node.hasAttribute(decision::DecisionWeightAttr())) {
      node.setAttribute(decision::DecisionWeightAttr(),computeAtomWeight(node));
    }
  }
}

uint64_t BitblastSolver::computeAtomWeight(TNode node) {
  NodeSet seen;
  return d_bitblaster->computeAtomWeight(node, seen);
}

void BitblastSolver::explain(TNode literal, std::vector<TNode>& assumptions) {
  d_bitblaster->explain(literal, assumptions);
}

void BitblastSolver::bitblastQueue() {
  while (!d_bitblastQueue.empty()) {
    TNode atom = d_bitblastQueue.front();
    d_bitblastQueue.pop();
    Debug("bv-bitblast-queue") << "BitblastSolver::bitblastQueue (" << atom << ")\n";
    if (options::bvAbstraction() &&
        d_abstractionModule->isLemmaAtom(atom)) {
      // don't bit-blast lemma atoms
      continue;
    }
    if( !utils::isBitblastAtom(atom) ){
      continue;
    }
    Debug("bitblast-queue") << "Bitblasting atom " << atom <<"\n";
    {
      TimerStat::CodeTimer codeTimer(d_bitblaster->d_statistics.d_bitblastTimer);
      d_bitblaster->bbAtom(atom);
    }
  }
}

bool BitblastSolver::check(Theory::Effort e)
{
  Debug("bv-bitblast") << "BitblastSolver::check (" << e << ")\n";
  Assert(options::bitblastMode() == options::BitblastMode::LAZY);

  ++(d_statistics.d_numCallstoCheck);

  Debug("bv-bitblast-debug") << "...process queue" << std::endl;
  //// Lazy bit-blasting
  // bit-blast enqueued nodes
  bitblastQueue();

  // Processing assertions
  while (!done())
  {
    TNode fact = get();
    d_validModelCache = false;
    Debug("bv-bitblast") << "  fact " << fact << ")\n";

    if (options::bvAbstraction())
    {
      // skip atoms that are the result of abstraction lemmas
      if (d_abstractionModule->isLemmaAtom(fact))
      {
        d_lemmaAtomsQueue.push_back(fact);
        continue;
      }
    }
    // skip facts involving integer equalities (from bv2nat)
    if (!utils::isBitblastAtom(fact))
    {
      continue;
    }

    if (!d_bv->inConflict()
        && (!d_bv->wasPropagatedBySubtheory(fact)
            || d_bv->getPropagatingSubtheory(fact) != SUB_BITBLAST))
    {
      // Some atoms have not been bit-blasted yet
      d_bitblaster->bbAtom(fact);
      // Assert to sat
      bool ok = d_bitblaster->assertToSat(fact, d_useSatPropagation);
      if (!ok)
      {
        std::vector<TNode> conflictAtoms;
        d_bitblaster->getConflict(conflictAtoms);
        setConflict(utils::mkAnd(conflictAtoms));
        return false;
      }
    }
  }

  Debug("bv-bitblast-debug") << "...do propagation" << std::endl;
  // We need to ensure we are fully propagated, so propagate now
  if (d_useSatPropagation)
  {
    d_bv->spendResource(ResourceManager::Resource::BvPropagationStep);
    bool ok = d_bitblaster->propagate();
    if (!ok)
    {
      std::vector<TNode> conflictAtoms;
      d_bitblaster->getConflict(conflictAtoms);
      setConflict(utils::mkAnd(conflictAtoms));
      return false;
    }
  }

  // Solving
  Debug("bv-bitblast-debug") << "...do solving" << std::endl;
  if (e == Theory::EFFORT_FULL)
  {
    Assert(!d_bv->inConflict());
    Debug("bitvector::bitblaster")
        << "BitblastSolver::addAssertions solving. \n";
    bool ok = d_bitblaster->solve();
    if (!ok)
    {
      std::vector<TNode> conflictAtoms;
      d_bitblaster->getConflict(conflictAtoms);
      Node conflict = utils::mkAnd(conflictAtoms);
      setConflict(conflict);
      return false;
    }
  }

  Debug("bv-bitblast-debug") << "...do abs bb" << std::endl;
  if (options::bvAbstraction() && e == Theory::EFFORT_FULL
      && d_lemmaAtomsQueue.size())
  {
    // bit-blast lemma atoms
    while (!d_lemmaAtomsQueue.empty())
    {
      TNode lemma_atom = d_lemmaAtomsQueue.front();
      d_lemmaAtomsQueue.pop();
      if (!utils::isBitblastAtom(lemma_atom))
      {
        continue;
      }
      d_bitblaster->bbAtom(lemma_atom);
      // Assert to sat and check for conflicts
      bool ok = d_bitblaster->assertToSat(lemma_atom, d_useSatPropagation);
      if (!ok)
      {
        std::vector<TNode> conflictAtoms;
        d_bitblaster->getConflict(conflictAtoms);
        setConflict(utils::mkAnd(conflictAtoms));
        return false;
      }
    }

    Assert(!d_bv->inConflict());
    bool ok = d_bitblaster->solve();
    if (!ok)
    {
      std::vector<TNode> conflictAtoms;
      d_bitblaster->getConflict(conflictAtoms);
      Node conflict = utils::mkAnd(conflictAtoms);
      setConflict(conflict);
      ++(d_statistics.d_numBBLemmas);
      return false;
    }
  }


  return true;
}

EqualityStatus BitblastSolver::getEqualityStatus(TNode a, TNode b) {
  return d_bitblaster->getEqualityStatus(a, b);
}

bool BitblastSolver::collectModelInfo(TheoryModel* m, bool fullModel)
{
  return d_bitblaster->collectModelInfo(m, fullModel);
}

Node BitblastSolver::getModelValue(TNode node)
{
  if (d_bv->d_invalidateModelCache.get()) {
    d_bitblaster->invalidateModelCache();
  }
  d_bv->d_invalidateModelCache.set(false);
  Node val = d_bitblaster->getTermModel(node, true);
  return val;
}



void BitblastSolver::setConflict(TNode conflict) {
  Node final_conflict = conflict;
  if (options::bitvectorQuickXplain() &&
      conflict.getKind() == kind::AND) {
    // std::cout << "Original conflict " << conflict.getNumChildren() << "\n";
    final_conflict = d_quickXplain->minimizeConflict(conflict);
    //std::cout << "Minimized conflict " << final_conflict.getNumChildren() << "\n";
  }
  d_bv->setConflict(final_conflict);
}

}/* namespace CVC4::theory::bv */
}/* namespace CVC4::theory */
}/* namespace CVC4 */
