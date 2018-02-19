/*********************                                                        */
/*! \file theory_fp.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Martin Brain, Paul Meng, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief [[ Add one-line brief description here ]]
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "cvc4_private.h"

#ifndef __CVC4__THEORY__FP__THEORY_FP_H
#define __CVC4__THEORY__FP__THEORY_FP_H

#include <string>
#include <utility>

#include "context/cdo.h"
#include "theory/fp/fp_converter.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace fp {

class TheoryFp : public Theory {
 public:
  /** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
  TheoryFp(context::Context* c, context::UserContext* u, OutputChannel& out,
           Valuation valuation, const LogicInfo& logicInfo);

  Node expandDefinition(LogicRequest& lr, Node node) override;

  void preRegisterTerm(TNode node) override;
  void addSharedTerm(TNode node) override;

  void check(Effort) override;

  Node getModelValue(TNode var) override;
  bool collectModelInfo(TheoryModel* m) override;

  std::string identify() const override { return "THEORY_FP"; }

  void setMasterEqualityEngine(eq::EqualityEngine* eq) override;

  Node explain(TNode n) override;

 protected:
  /** Equality engine */
  class NotifyClass : public eq::EqualityEngineNotify {
   protected:
    TheoryFp& d_theorySolver;

   public:
    NotifyClass(TheoryFp& solver) : d_theorySolver(solver) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value);
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2,
                                     bool value);
    void eqNotifyConstantTermMerge(TNode t1, TNode t2);
    void eqNotifyNewClass(TNode t) {}
    void eqNotifyPreMerge(TNode t1, TNode t2) {}
    void eqNotifyPostMerge(TNode t1, TNode t2) {}
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) {}
  };
  friend NotifyClass;

  NotifyClass d_notification;
  eq::EqualityEngine d_equalityEngine;

  /** General utility **/
  void registerTerm(TNode node);
  bool isRegistered(TNode node);

  context::CDHashSet<Node, NodeHashFunction> d_registeredTerms;

  /** Bit-blasting conversion */
  FpConverter d_conv;
  bool d_expansionRequested;

  void convertAndEquateTerm(TNode node);

  /** Interaction with the rest of the solver **/
  void handleLemma(Node node);
  bool handlePropagation(TNode node);
  void handleConflict(TNode node);

  context::CDO<bool> d_conflict;
  context::CDO<Node> d_conflictNode;

  /** Uninterpretted functions for partially defined functions. **/
  typedef context::CDHashMap<TypeNode, Node, TypeNodeHashFunction>
      ComparisonUFMap;

  ComparisonUFMap d_minMap;
  ComparisonUFMap d_maxMap;

  Node minUF(Node);
  Node maxUF(Node);

  typedef context::CDHashMap<std::pair<TypeNode, TypeNode>, Node,
                             PairTypeNodeHashFunction>
      ConversionUFMap;

  ConversionUFMap d_toUBVMap;
  ConversionUFMap d_toSBVMap;

  Node toUBVUF(Node);
  Node toSBVUF(Node);

  ComparisonUFMap d_toRealMap;

  Node toRealUF(Node);
}; /* class TheoryFp */

}  // namespace fp
}  // namespace theory
}  // namespace CVC4

#endif /* __CVC4__THEORY__FP__THEORY_FP_H */
