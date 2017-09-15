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

#include "theory/theory.h"
#include "theory/uf/equality_engine.h"

#include "theory/fp/fp_converter.h"

#include "context/cdo.h"

namespace CVC4 {
namespace theory {
namespace fp {

class TheoryFp : public Theory {
protected :
  /** Equality engine */
  class NotifyClass : public eq::EqualityEngineNotify {
    protected :
      TheoryFp& theorySolver;

    public:
    NotifyClass(TheoryFp& solver): theorySolver(solver) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value);
    bool eqNotifyTriggerPredicate(TNode predicate, bool value);
    bool eqNotifyTriggerTermEquality(TheoryId tag, TNode t1, TNode t2, bool value);
    void eqNotifyConstantTermMerge(TNode t1, TNode t2);
    void eqNotifyNewClass(TNode t) { }
    void eqNotifyPreMerge(TNode t1, TNode t2) { }
    void eqNotifyPostMerge(TNode t1, TNode t2) { }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) { }
  };
  friend NotifyClass;

  NotifyClass notification;
  eq::EqualityEngine equalityEngine;


  /** General utility **/
  void registerTerm(TNode node);
  bool isRegistered(TNode node);

  context::CDHashSet<Node, NodeHashFunction> registeredTerms;


  /** Bit-blasting conversion */
  fpConverter conv;
  bool expansionRequested;

  void convertAndEquateTerm(TNode node);


  /** Interaction with the rest of the solver **/
  void handleLemma(Node node);
  bool handlePropagation(TNode node);
  void handleConflict(TNode node);

  context::CDO<bool> conflict;
  context::CDO<Node> conflictNode;

  /** Uninterpretted functions for partially defined functions. **/
  typedef context::CDHashMap<TypeNode, Node, TypeNodeHashFunction> comparisonUFMap;

  comparisonUFMap minMap;
  comparisonUFMap maxMap;

  Node minUF(Node);
  Node maxUF(Node);

  typedef context::CDHashMap<std::pair<TypeNode, TypeNode>, Node, PairTypeNodeHashFunction> conversionUFMap;

  conversionUFMap toUBVMap;
  conversionUFMap toSBVMap;

  Node toUBVUF(Node);
  Node toSBVUF(Node);


  comparisonUFMap toRealMap;

  Node toRealUF(Node);


public:

  /** Constructs a new instance of TheoryFp w.r.t. the provided contexts. */
  TheoryFp(context::Context* c,
           context::UserContext* u,
           OutputChannel& out,
           Valuation valuation,
           const LogicInfo& logicInfo);

  Node expandDefinition(LogicRequest &lr, Node node);

  void preRegisterTerm(TNode node);
  void addSharedTerm(TNode node);

  void check(Effort);

  Node getModelValue(TNode var);
  void collectModelInfo(TheoryModel *m);

  std::string identify() const {
    return "THEORY_FP";
  }

  void setMasterEqualityEngine(eq::EqualityEngine* eq);

  Node explain(TNode n);

};/* class TheoryFp */

}/* CVC4::theory::fp namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__FP__THEORY_FP_H */
