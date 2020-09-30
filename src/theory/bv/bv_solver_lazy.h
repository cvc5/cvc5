/*********************                                                        */
/*! \file bv_solver_lazy.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner, Liana Hadarean, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Lazy bit-vector solver.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__BV_SOLVER_LAZY_H
#define CVC4__THEORY__BV__BV_SOLVER_LAZY_H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "theory/bv/bv_solver.h"
#include "theory/bv/bv_subtheory.h"
#include "theory/bv/theory_bv.h"
#include "util/hash.h"

namespace CVC4 {
namespace theory {
namespace bv {

class CoreSolver;
class InequalitySolver;
class AlgebraicSolver;
class BitblastSolver;
class EagerBitblastSolver;
class AbstractionModule;

class BVSolverLazy : public BVSolver
{
  /** Back reference to TheoryBV */
  TheoryBV& d_bv;

  /** The context we are using */
  context::Context* d_context;

  /** Context dependent set of atoms we already propagated */
  context::CDHashSet<Node, NodeHashFunction> d_alreadyPropagatedSet;
  context::CDHashSet<Node, NodeHashFunction> d_sharedTermsSet;

  std::vector<std::unique_ptr<SubtheorySolver>> d_subtheories;
  std::unordered_map<SubTheory, SubtheorySolver*, std::hash<int>>
      d_subtheoryMap;

 public:
  BVSolverLazy(TheoryBV& bv,
               context::Context* c,
               context::UserContext* u,
               ProofNodeManager* pnm = nullptr,
               std::string name = "");

  ~BVSolverLazy();

  //--------------------------------- initialization

  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;

  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization

  void preRegisterTerm(TNode n) override;

  bool preCheck(Theory::Effort e) override;

  bool needsCheckLastEffort() override;

  void propagate(Theory::Effort e) override;

  TrustNode explain(TNode n) override;

  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  std::string identify() const override { return std::string("BVSolverLazy"); }

  Theory::PPAssertStatus ppAssert(TNode in,
                                  SubstitutionMap& outSubstitutions) override;

  TrustNode ppRewrite(TNode t) override;

  void ppStaticLearn(TNode in, NodeBuilder<>& learned) override;

  void presolve() override;

  bool applyAbstraction(const std::vector<Node>& assertions,
                        std::vector<Node>& new_assertions) override;

  bool isLeaf(TNode node) { return d_bv.isLeaf(node); }

 private:
  class Statistics
  {
   public:
    AverageStat d_avgConflictSize;
    IntStat d_solveSubstitutions;
    TimerStat d_solveTimer;
    IntStat d_numCallsToCheckFullEffort;
    IntStat d_numCallsToCheckStandardEffort;
    TimerStat d_weightComputationTimer;
    IntStat d_numMultSlice;
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

  void check(Theory::Effort e);
  void spendResource(ResourceManager::Resource r);

  typedef std::unordered_set<TNode, TNodeHashFunction> TNodeSet;
  typedef std::unordered_set<Node, NodeHashFunction> NodeSet;
  NodeSet d_staticLearnCache;

  typedef std::unordered_map<Node, Node, NodeHashFunction> NodeToNode;

  context::CDO<bool> d_lemmasAdded;

  // Are we in conflict?
  context::CDO<bool> d_conflict;

  // Invalidate the model cache if check was called
  context::CDO<bool> d_invalidateModelCache;

  /** The conflict node */
  Node d_conflictNode;

  /** Literals to propagate */
  context::CDList<Node> d_literalsToPropagate;

  /** Index of the next literal to propagate */
  context::CDO<unsigned> d_literalsToPropagateIndex;

  /**
   * Keeps a map from nodes to the subtheory that propagated it so that we can
   * explain it properly.
   */
  typedef context::CDHashMap<Node, SubTheory, NodeHashFunction> PropagatedMap;
  PropagatedMap d_propagatedBy;

  std::unique_ptr<EagerBitblastSolver> d_eagerSolver;
  std::unique_ptr<AbstractionModule> d_abstractionModule;
  bool d_calledPreregister;

  bool wasPropagatedBySubtheory(TNode literal) const
  {
    return d_propagatedBy.find(literal) != d_propagatedBy.end();
  }

  SubTheory getPropagatingSubtheory(TNode literal) const
  {
    Assert(wasPropagatedBySubtheory(literal));
    PropagatedMap::const_iterator find = d_propagatedBy.find(literal);
    return (*find).second;
  }

  /** Should be called to propagate the literal.  */
  bool storePropagation(TNode literal, SubTheory subtheory);

  /**
   * Explains why this literal (propagated by subtheory) is true by adding
   * assumptions.
   */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  void notifySharedTerm(TNode t) override;

  bool isSharedTerm(TNode t) { return d_sharedTermsSet.contains(t); }

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  Node getModelValue(TNode var);

  inline std::string indent()
  {
    std::string indentStr(d_context->getLevel(), ' ');
    return indentStr;
  }

  void setConflict(Node conflict = Node::null());

  bool inConflict() { return d_conflict; }

  void sendConflict();

  void lemma(TNode node)
  {
    d_inferManager.lemma(node);
    d_lemmasAdded = true;
  }

  void checkForLemma(TNode node);

  size_t numAssertions() { return d_bv.numAssertions(); }

  theory::Assertion get() { return d_bv.get(); }

  bool done() { return d_bv.done(); }

  friend class LazyBitblaster;
  friend class TLazyBitblaster;
  friend class EagerBitblaster;
  friend class BitblastSolver;
  friend class EqualitySolver;
  friend class CoreSolver;
  friend class InequalitySolver;
  friend class AlgebraicSolver;
  friend class EagerBitblastSolver;
}; /* class BVSolverLazy */

}  // namespace bv
}  // namespace theory

}  // namespace CVC4

#endif /* CVC4__THEORY__BV__BV_SOLVER_LAZY_H */
