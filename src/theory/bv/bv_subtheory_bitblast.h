/*********************                                                        */
/*! \file bv_subtheory_bitblast.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Dejan Jovanovic
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

#include "cvc4_private.h"

#pragma once

#include <unordered_map>

#include "theory/bv/bv_subtheory.h"

namespace CVC4 {

namespace theory {
namespace bv {

class TLazyBitblaster;
class AbstractionModule;
class BVQuickCheck;
class QuickXPlain;

/**
 * BitblastSolver
 */
class BitblastSolver : public SubtheorySolver
{
  struct Statistics
  {
    IntStat d_numCallstoCheck;
    IntStat d_numBBLemmas;
    Statistics();
    ~Statistics();
  };
  /** Bitblaster */
  std::unique_ptr<TLazyBitblaster> d_bitblaster;

  /** Nodes that still need to be bit-blasted */
  context::CDQueue<TNode> d_bitblastQueue;
  Statistics d_statistics;

  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeMap;
  NodeMap d_modelCache;
  context::CDO<bool> d_validModelCache;

  /** Queue for bit-blasting lemma atoms only in full check if we are sat */
  context::CDQueue<TNode> d_lemmaAtomsQueue;
  bool d_useSatPropagation;
  AbstractionModule* d_abstractionModule;
  std::unique_ptr<BVQuickCheck> d_quickCheck;
  std::unique_ptr<QuickXPlain> d_quickXplain;
  //  Node getModelValueRec(TNode node);
  void setConflict(TNode conflict);

 public:
  BitblastSolver(context::Context* c, BVSolverLazy* bv);
  ~BitblastSolver();

  void preRegister(TNode node) override;
  bool check(Theory::Effort e) override;
  void explain(TNode literal, std::vector<TNode>& assumptions) override;
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  Node getModelValue(TNode node) override;
  bool isComplete() override { return true; }
  void bitblastQueue();
  void setAbstraction(AbstractionModule* module);
  uint64_t computeAtomWeight(TNode atom);
};

}  // namespace bv
}  // namespace theory
} /* namespace CVC4 */
