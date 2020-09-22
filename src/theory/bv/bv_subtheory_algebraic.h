/*********************                                                        */
/*! \file bv_subtheory_algebraic.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
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
#include <unordered_set>

#include "theory/bv/bv_subtheory.h"
#include "theory/bv/slicer.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace theory {
namespace bv {

class AlgebraicSolver;

Node mergeExplanations(TNode expl1, TNode expl2);
Node mergeExplanations(const std::vector<Node>& expls);

/**
 * Non-context dependent substitution with explanations.
 *
 */
class SubstitutionEx
{
  struct SubstitutionElement
  {
    Node to;
    Node reason;
    SubstitutionElement() : to(), reason() {}

    SubstitutionElement(TNode t, TNode r) : to(t), reason(r) {}
  };

  struct SubstitutionStackElement
  {
    TNode node;
    bool childrenAdded;
    SubstitutionStackElement(TNode n, bool ca = false)
        : node(n), childrenAdded(ca)
    {
    }
  };

  typedef std::unordered_map<Node, SubstitutionElement, NodeHashFunction>
      Substitutions;
  typedef std::unordered_map<Node, SubstitutionElement, NodeHashFunction>
      SubstitutionsCache;

  Substitutions d_substitutions;
  SubstitutionsCache d_cache;
  bool d_cacheInvalid;
  theory::SubstitutionMap* d_modelMap;

  Node getReason(TNode node) const;
  bool hasCache(TNode node) const;
  Node getCache(TNode node) const;
  void storeCache(TNode from, TNode to, Node rason);
  Node internalApply(TNode node);

 public:
  SubstitutionEx(theory::SubstitutionMap* modelMap);
  /**
   * Returnst true if the substitution map did not contain from.
   *
   * @param from
   * @param to
   * @param reason
   *
   * @return
   */
  bool addSubstitution(TNode from, TNode to, TNode reason);
  Node apply(TNode node);
  Node explain(TNode node) const;
};

/**
 * In-processing worklist element, id keeps track of
 * original assertion.
 *
 */
struct WorklistElement
{
  Node node;
  unsigned id;
  WorklistElement(Node n, unsigned i) : node(n), id(i) {}
  WorklistElement() : node(), id(-1) {}
};

typedef std::unordered_map<Node, Node, NodeHashFunction> NodeNodeMap;
typedef std::unordered_map<Node, unsigned, NodeHashFunction> NodeIdMap;
typedef std::unordered_set<TNode, TNodeHashFunction> TNodeSet;

class ExtractSkolemizer
{
  struct Extract
  {
    unsigned high;
    unsigned low;
    Extract(unsigned h, unsigned l) : high(h), low(l) {}
  };

  struct ExtractList
  {
    Base base;
    std::vector<Extract> extracts;
    ExtractList(unsigned bitwidth) : base(bitwidth), extracts() {}
    ExtractList() : base(1), extracts() {}
    void addExtract(Extract& e);
  };
  typedef std::unordered_map<Node, ExtractList, NodeHashFunction> VarExtractMap;
  context::Context d_emptyContext;
  VarExtractMap d_varToExtract;
  theory::SubstitutionMap* d_modelMap;
  theory::SubstitutionMap d_skolemSubst;
  theory::SubstitutionMap d_skolemSubstRev;

  void storeSkolem(TNode node, TNode skolem);
  void storeExtract(TNode var, unsigned high, unsigned low);
  void collectExtracts(TNode node, TNodeSet& seen);
  Node skolemize(TNode);
  Node unSkolemize(TNode);

  Node mkSkolem(Node node);

 public:
  ExtractSkolemizer(theory::SubstitutionMap* modelMap);
  void skolemize(std::vector<WorklistElement>&);
  void unSkolemize(std::vector<WorklistElement>&);
  ~ExtractSkolemizer();
};

class BVQuickCheck;
class QuickXPlain;

/**
 * AlgebraicSolver
 */
class AlgebraicSolver : public SubtheorySolver
{
  struct Statistics
  {
    IntStat d_numCallstoCheck;
    IntStat d_numSimplifiesToTrue;
    IntStat d_numSimplifiesToFalse;
    IntStat d_numUnsat;
    IntStat d_numSat;
    IntStat d_numUnknown;
    TimerStat d_solveTime;
    BackedStat<double> d_useHeuristic;
    Statistics();
    ~Statistics();
  };

  std::unique_ptr<SubstitutionMap> d_modelMap;
  std::unique_ptr<BVQuickCheck> d_quickSolver;
  context::CDO<bool> d_isComplete;
  context::CDO<bool>
      d_isDifficult; /**< flag to indicate whether the current assertions
                        contain expensive BV operators */

  unsigned long d_budget;
  std::vector<Node> d_explanations; /**< explanations for assertions indexed by
                                       assertion id */
  TNodeSet d_inputAssertions; /**< assertions in current context (for debugging
                                 purposes only) */
  NodeIdMap d_ids;            /**< map from assertions to ids */
  uint64_t d_numSolved;
  uint64_t d_numCalls;

  /** separate quickXplain module as it can reuse the current SAT solver */
  std::unique_ptr<QuickXPlain> d_quickXplain;

  Statistics d_statistics;
  bool useHeuristic();
  void setConflict(TNode conflict);
  bool isSubstitutableIn(TNode node, TNode in);
  bool checkExplanation(TNode expl);
  void storeExplanation(TNode expl);
  void storeExplanation(unsigned id, TNode expl);
  /**
   * Apply substitutions and rewriting to the worklist assertions to a fixpoint.
   * Subsitutions learned store in subst.
   *
   * @param worklist
   * @param subst
   */
  void processAssertions(std::vector<WorklistElement>& worklist,
                         SubstitutionEx& subst);
  /**
   * Attempt to solve the equation in fact, and if successful
   * add a substitution to subst.
   *
   * @param fact equation we are trying to solve
   * @param reason the reason in terms of original assertions
   * @param subst substitution map
   *
   * @return true if added a substitution to subst
   */
  bool solve(TNode fact, TNode reason, SubstitutionEx& subst);
  /**
   * Run a SAT solver on the given facts with the given budget.
   * Sets the isComplete flag and conflict accordingly.
   *
   * @param facts
   *
   * @return true if no conflict was detected.
   */
  bool quickCheck(std::vector<Node>& facts);

 public:
  AlgebraicSolver(context::Context* c, BVSolverLazy* bv);
  ~AlgebraicSolver();

  void preRegister(TNode node) override {}
  bool check(Theory::Effort e) override;
  void explain(TNode literal, std::vector<TNode>& assumptions) override
  {
    Unreachable() << "AlgebraicSolver does not propagate.\n";
  }
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;
  Node getModelValue(TNode node) override;
  bool isComplete() override;
  void assertFact(TNode fact) override;
};

}  // namespace bv
}  // namespace theory
}  // namespace CVC4
