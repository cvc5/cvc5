/*********************                                                        */
/*! \file bv_subtheory_core.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Mathias Preiner, Tim King
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
#include <unordered_set>

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "theory/bv/bv_subtheory.h"
#include "theory/ext_theory.h"

namespace CVC4 {
namespace theory {
namespace bv {

class Base;

/** An extended theory callback used by the core solver */
class CoreSolverExtTheoryCallback : public ExtTheoryCallback
{
 public:
  CoreSolverExtTheoryCallback() : d_equalityEngine(nullptr) {}
  /** Get current substitution based on the underlying equality engine. */
  bool getCurrentSubstitution(int effort,
                              const std::vector<Node>& vars,
                              std::vector<Node>& subs,
                              std::map<Node, std::vector<Node> >& exp) override;
  /** Get reduction. */
  bool getReduction(int effort, Node n, Node& nr, bool& satDep) override;
  /** The underlying equality engine */
  eq::EqualityEngine* d_equalityEngine;
};

/**
 * Bitvector equality solver
 */
class CoreSolver : public SubtheorySolver {
  typedef std::unordered_map<TNode, Node, TNodeHashFunction> ModelValue;
  typedef std::unordered_map<TNode, bool, TNodeHashFunction> TNodeBoolMap;
  typedef std::unordered_set<TNode, TNodeHashFunction> TNodeSet;


  struct Statistics {
    IntStat d_numCallstoCheck;
    Statistics();
    ~Statistics();
  };

  // NotifyClass: handles call-back from congruence closure module
  class NotifyClass : public eq::EqualityEngineNotify {
    CoreSolver& d_solver;

  public:
    NotifyClass(CoreSolver& solver): d_solver(solver) {}
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override {}
    void eqNotifyMerge(TNode t1, TNode t2) override {}
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override {}
  };


  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** Store a propagation to the bv solver */
  bool storePropagation(TNode literal);

  /** Store a conflict from merging two constants */
  void conflict(TNode a, TNode b);

  context::CDO<bool> d_isComplete;
  unsigned d_lemmaThreshold;

  bool d_preregisterCalled;
  bool d_checkCalled;

  /** Pointer to the parent theory solver that owns this */
  TheoryBV* d_bv;
  /** Pointer to the equality engine of the parent */
  eq::EqualityEngine* d_equalityEngine;
  /** The extended theory callback */
  CoreSolverExtTheoryCallback d_extTheoryCb;
  /** Extended theory module, for context-dependent simplification. */
  std::unique_ptr<ExtTheory> d_extTheory;

  /** To make sure we keep the explanations */
  context::CDHashSet<Node, NodeHashFunction> d_reasons;
  ModelValue d_modelValues;
  void buildModel();
  bool assertFactToEqualityEngine(TNode fact, TNode reason);
  bool decomposeFact(TNode fact);
  Node getBaseDecomposition(TNode a);
  bool isCompleteForTerm(TNode term, TNodeBoolMap& seen);
  Statistics d_statistics;

  /** Whether we need a last call effort check */
  bool d_needsLastCallCheck;
  /** For extended functions */
  context::CDHashSet<Node, NodeHashFunction> d_extf_range_infer;
  context::CDHashSet<Node, NodeHashFunction> d_extf_collapse_infer;

  /** do extended function inferences
   *
   * This method adds lemmas on the output channel of TheoryBV based on
   * reasoning about extended functions, such as bv2nat and int2bv. Examples
   * of lemmas added by this method include:
   *   0 <= ((_ int2bv w) x) < 2^w
   *   ((_ int2bv w) (bv2nat x)) = x
   *   (bv2nat ((_ int2bv w) x)) == x + k*2^w
   * The purpose of these lemmas is to recognize easy conflicts before fully
   * reducing extended functions based on their full semantics.
   */
  bool doExtfInferences(std::vector<Node>& terms);
  /** do extended function reductions
   *
   * This method adds lemmas on the output channel of TheoryBV based on
   * reducing all extended function applications that are preregistered to
   * this theory and have not already been reduced by context-dependent
   * simplification (see theory/ext_theory.h). Examples of lemmas added by
   * this method include:
   *   (bv2nat x) = (ite ((_ extract w w-1) x) 2^{w-1} 0) + ... +
   *                (ite ((_ extract 1 0) x) 1 0)
   */
  bool doExtfReductions(std::vector<Node>& terms);

 public:
  CoreSolver(context::Context* c, TheoryBV* bv);
  ~CoreSolver();
  bool needsEqualityEngine(EeSetupInfo& esi);
  void finishInit();
  bool isComplete() override { return d_isComplete; }
  void preRegister(TNode node) override;
  bool check(Theory::Effort e) override;
  void explain(TNode literal, std::vector<TNode>& assumptions) override;
  bool collectModelInfo(TheoryModel* m, bool fullModel) override;
  Node getModelValue(TNode var) override;
  void addSharedTerm(TNode t) override;
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  bool hasTerm(TNode node) const;
  void addTermToEqualityEngine(TNode node);
  /** check extended functions at the given effort */
  void checkExtf(Theory::Effort e);
  bool needsCheckLastEffort() const;
};

}
}
}
