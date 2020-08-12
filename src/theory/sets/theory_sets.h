/*********************                                                        */
/*! \file theory_sets.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Tim King, Kshitij Bansal, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Sets theory.
 **
 ** Sets theory.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__SETS__THEORY_SETS_H
#define CVC4__THEORY__SETS__THEORY_SETS_H

#include <memory>

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace sets {

class TheorySetsPrivate;
class TheorySetsScrutinize;

class TheorySets : public Theory
{
  friend class TheorySetsPrivate;
  friend class TheorySetsRels;
 public:
  /** Constructs a new instance of TheorySets w.r.t. the provided contexts. */
  TheorySets(context::Context* c,
             context::UserContext* u,
             OutputChannel& out,
             Valuation valuation,
             const LogicInfo& logicInfo,
             ProofNodeManager* pnm);
  ~TheorySets() override;

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization

  void addSharedTerm(TNode) override;
  void check(Effort) override;
  bool collectModelInfo(TheoryModel* m) override;
  void computeCareGraph() override;
  TrustNode explain(TNode) override;
  EqualityStatus getEqualityStatus(TNode a, TNode b) override;
  Node getModelValue(TNode) override;
  std::string identify() const override { return "THEORY_SETS"; }
  void preRegisterTerm(TNode node) override;
  TrustNode expandDefinition(Node n) override;
  PPAssertStatus ppAssert(TNode in, SubstitutionMap& outSubstitutions) override;
  void presolve() override;
  void propagate(Effort) override;
  void setMasterEqualityEngine(eq::EqualityEngine* eq) override;
  bool isEntailed(Node n, bool pol);
  /* equality engine */
  virtual eq::EqualityEngine* getEqualityEngine() override;
 private:
  /** Functions to handle callbacks from equality engine */
  class NotifyClass : public eq::EqualityEngineNotify
  {
   public:
    NotifyClass(TheorySetsPrivate& theory) : d_theory(theory) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) override;
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override;
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override;
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override;
    void eqNotifyNewClass(TNode t) override;
    void eqNotifyPreMerge(TNode t1, TNode t2) override;
    void eqNotifyPostMerge(TNode t1, TNode t2) override;
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override;
    
   private:
    TheorySetsPrivate& d_theory;
  };
  /** The internal theory */
  std::unique_ptr<TheorySetsPrivate> d_internal;
  /** Instance of the above class */
  NotifyClass d_notify;  
  /** Equality engine */
  eq::EqualityEngine d_equalityEngine;
}; /* class TheorySets */

}/* CVC4::theory::sets namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__SETS__THEORY_SETS_H */
