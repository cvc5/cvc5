/*********************                                                        */
/*! \file theory_bv.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Bitvector theory.
 **
 ** Bitvector theory.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BV__THEORY_BV_H
#define CVC4__THEORY__BV__THEORY_BV_H

#include <unordered_map>
#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/context.h"
#include "theory/bv/bv_subtheory.h"
#include "theory/bv/theory_bv_rewriter.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/theory.h"
#include "util/hash.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace theory {
namespace bv {

class CoreSolver;
class InequalitySolver;
class AlgebraicSolver;
class BitblastSolver;

class EagerBitblastSolver;

class AbstractionModule;

class TheoryBV : public Theory {

  /** The context we are using */
  context::Context* d_context;

  /** Context dependent set of atoms we already propagated */
  context::CDHashSet<Node, NodeHashFunction> d_alreadyPropagatedSet;
  context::CDHashSet<Node, NodeHashFunction> d_sharedTermsSet;

  std::vector<std::unique_ptr<SubtheorySolver>> d_subtheories;
  std::unordered_map<SubTheory, SubtheorySolver*, std::hash<int> > d_subtheoryMap;

 public:
  TheoryBV(context::Context* c,
           context::UserContext* u,
           OutputChannel& out,
           Valuation valuation,
           const LogicInfo& logicInfo,
           ProofNodeManager* pnm = nullptr,
           std::string name = "");

  ~TheoryBV();

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization

  TrustNode expandDefinition(Node node) override;

  void preRegisterTerm(TNode n) override;

  void check(Effort e) override;

  bool needsCheckLastEffort() override;

  void propagate(Effort e) override;

  TrustNode explain(TNode n) override;

  bool collectModelInfo(TheoryModel* m) override;

  std::string identify() const override { return std::string("TheoryBV"); }

  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions) override;

  TrustNode ppRewrite(TNode t) override;

  void ppStaticLearn(TNode in, NodeBuilder<>& learned) override;

  void presolve() override;

  bool applyAbstraction(const std::vector<Node>& assertions,
                        std::vector<Node>& new_assertions);

 private:
  class Statistics
  {
   public:
    AverageStat d_avgConflictSize;
    IntStat     d_solveSubstitutions;
    TimerStat   d_solveTimer;
    IntStat     d_numCallsToCheckFullEffort;
    IntStat     d_numCallsToCheckStandardEffort;
    TimerStat   d_weightComputationTimer;
    IntStat     d_numMultSlice;
    Statistics();
    ~Statistics();
  };

  Statistics d_statistics;

  void spendResource(ResourceManager::Resource r);

  /**
   * Return the uninterpreted function symbol corresponding to division-by-zero
   * for this particular bit-width
   * @param k should be UREM or UDIV
   * @param width
   *
   * @return
   */
  Node getBVDivByZero(Kind k, unsigned width);

  typedef std::unordered_set<TNode, TNodeHashFunction> TNodeSet;
  typedef std::unordered_set<Node, NodeHashFunction> NodeSet;
  NodeSet d_staticLearnCache;

  /**
   * Maps from bit-vector width to division-by-zero uninterpreted
   * function symbols.
   */
  std::unordered_map<unsigned, Node> d_BVDivByZero;
  std::unordered_map<unsigned, Node> d_BVRemByZero;

  typedef std::unordered_map<Node, Node, NodeHashFunction>  NodeToNode;

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
   * Keeps a map from nodes to the subtheory that propagated it so that we can explain it
   * properly.
   */
  typedef context::CDHashMap<Node, SubTheory, NodeHashFunction> PropagatedMap;
  PropagatedMap d_propagatedBy;

  std::unique_ptr<EagerBitblastSolver> d_eagerSolver;
  std::unique_ptr<AbstractionModule> d_abstractionModule;
  bool d_calledPreregister;

  bool wasPropagatedBySubtheory(TNode literal) const {
    return d_propagatedBy.find(literal) != d_propagatedBy.end();
  }

  SubTheory getPropagatingSubtheory(TNode literal) const {
    Assert(wasPropagatedBySubtheory(literal));
    PropagatedMap::const_iterator find = d_propagatedBy.find(literal);
    return (*find).second;
  }

  /** Should be called to propagate the literal.  */
  bool storePropagation(TNode literal, SubTheory subtheory);

  /**
   * Explains why this literal (propagated by subtheory) is true by adding assumptions.
   */
  void explain(TNode literal, std::vector<TNode>& assumptions);

  void notifySharedTerm(TNode t) override;

  bool isSharedTerm(TNode t) { return d_sharedTermsSet.contains(t); }

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  Node getModelValue(TNode var) override;

  inline std::string indent()
  {
    std::string indentStr(getSatContext()->getLevel(), ' ');
    return indentStr;
  }

  void setConflict(Node conflict = Node::null());

  bool inConflict() {
    return d_conflict;
  }

  void sendConflict();

  void lemma(TNode node)
  {
    d_out->lemma(node);
    d_lemmasAdded = true;
  }

  void checkForLemma(TNode node);

  /** The theory rewriter for this theory. */
  TheoryBVRewriter d_rewriter;
  /** A (default) theory state object */
  TheoryState d_state;

  friend class LazyBitblaster;
  friend class TLazyBitblaster;
  friend class EagerBitblaster;
  friend class BitblastSolver;
  friend class EqualitySolver;
  friend class CoreSolver;
  friend class InequalitySolver;
  friend class AlgebraicSolver;
  friend class EagerBitblastSolver;
};/* class TheoryBV */

}/* CVC4::theory::bv namespace */
}/* CVC4::theory namespace */

}/* CVC4 namespace */

#endif /* CVC4__THEORY__BV__THEORY_BV_H */
