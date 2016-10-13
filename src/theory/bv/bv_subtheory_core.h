/*********************                                                        */
/*! \file bv_subtheory_core.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Liana Hadarean, Andrew Reynolds, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2016 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Algebraic solver.
 **
 ** Algebraic solver.
 **/

#pragma once

#include "cvc4_private.h"
#include "theory/bv/bv_subtheory.h"
#include "context/cdhashmap.h"
#include "context/cdhashset.h"

namespace CVC4 {
namespace theory {
namespace bv {

class Slicer;
class Base;
/**
 * Bitvector equality solver
 */
class CoreSolver : public SubtheorySolver {
  typedef __gnu_cxx::hash_map<TNode, Node, TNodeHashFunction> ModelValue;
  typedef __gnu_cxx::hash_map<TNode, bool, TNodeHashFunction> TNodeBoolMap;
  typedef __gnu_cxx::hash_set<TNode, TNodeHashFunction> TNodeSet;


  struct Statistics {
    IntStat d_numCallstoCheck;
    BackedStat<bool> d_slicerEnabled;
    Statistics();
    ~Statistics();
  };

  // NotifyClass: handles call-back from congruence closure module
  class NotifyClass : public eq::EqualityEngineNotify {
    CoreSolver& d_solver;

  public:
    NotifyClass(CoreSolver& solver): d_solver(solver) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value);
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value);
    void eqNotifyConstantTermMerge(TNode t1, TNode t2);
    void eqNotifyNewClass(TNode t);
    void eqNotifyPreMerge(TNode t1, TNode t2) { }
    void eqNotifyPostMerge(TNode t1, TNode t2) { }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { }
  };


  /** The notify class for d_equalityEngine */
  NotifyClass d_notify;

  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;

  /** Store a propagation to the bv solver */
  bool storePropagation(TNode literal);

  /** Store a conflict from merging two constants */
  void conflict(TNode a, TNode b);

  /** new equivalence class */
  void eqNotifyNewClass(TNode t);

  Slicer* d_slicer;
  context::CDO<bool> d_isComplete;
  unsigned d_lemmaThreshold;
  
  /** Used to ensure that the core slicer is used properly*/
  bool d_useSlicer;
  bool d_preregisterCalled;
  bool d_checkCalled;
  
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
  CoreSolver(context::Context* c, TheoryBV* bv);
  ~CoreSolver();
  bool  isComplete() { return d_isComplete; }
  void  setMasterEqualityEngine(eq::EqualityEngine* eq);
  void  preRegister(TNode node);
  bool  check(Theory::Effort e);
  void  explain(TNode literal, std::vector<TNode>& assumptions);
  void  collectModelInfo(TheoryModel* m, bool fullModel);
  Node  getModelValue(TNode var);
  void  addSharedTerm(TNode t) {
    d_equalityEngine.addTriggerTerm(t, THEORY_BV);
  }
  EqualityStatus getEqualityStatus(TNode a, TNode b) {
    if (d_equalityEngine.areEqual(a, b)) {
      // The terms are implied to be equal
      return EQUALITY_TRUE;
    }
    if (d_equalityEngine.areDisequal(a, b, false)) {
      // The terms are implied to be dis-equal
      return EQUALITY_FALSE;
    }
    return EQUALITY_UNKNOWN;
  }
  bool hasTerm(TNode node) const { return d_equalityEngine.hasTerm(node); }
  void addTermToEqualityEngine(TNode node) { d_equalityEngine.addTerm(node); }
  void enableSlicer();
  eq::EqualityEngine * getEqualityEngine() { return &d_equalityEngine; }
};


}
}
}
