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
  /** Pointer to the extended theory module. */
  ExtTheory* d_extTheory;

  /** To make sure we keep the explanations */
  context::CDHashSet<Node, NodeHashFunction> d_reasons;
  ModelValue d_modelValues;
  void buildModel();
  bool assertFactToEqualityEngine(TNode fact, TNode reason);
  bool decomposeFact(TNode fact);
  Node getBaseDecomposition(TNode a);
  bool isCompleteForTerm(TNode term, TNodeBoolMap& seen);
  Statistics d_statistics;

 public:
  CoreSolver(context::Context* c, TheoryBV* bv, ExtTheory* extt);
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
};


}
}
}
