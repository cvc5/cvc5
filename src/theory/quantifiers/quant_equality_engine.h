/*********************                                                        */
/*! \file quant_equality_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Paul Meng, Tim King
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Congruence closure with free variables
 **/

#include "cvc4_private.h"

#ifndef __CVC4__QUANTIFIERS_EQUALITY_ENGINE_H
#define __CVC4__QUANTIFIERS_EQUALITY_ENGINE_H

#include <iostream>
#include <string>
#include <vector>
#include <map>
#include "expr/node.h"
#include "expr/type_node.h"
#include "theory/quantifiers_engine.h"

namespace CVC4 {
namespace theory {
namespace quantifiers {

class QuantEqualityEngine : public QuantifiersModule {
  typedef context::CDHashMap<Node, bool, NodeHashFunction> NodeBoolMap;
private:
  //notification class for equality engine
  class NotifyClass : public eq::EqualityEngineNotify {
    QuantEqualityEngine& d_qee;
  public:
    NotifyClass(QuantEqualityEngine& qee): d_qee(qee) {}
    bool eqNotifyTriggerEquality(TNode equality, bool value) override
    {
      return true;
    }
    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
    {
      return true;
    }
    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      return true;
    }
    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
    {
      d_qee.conflict(t1, t2);
    }
    void eqNotifyNewClass(TNode t) override { d_qee.eqNotifyNewClass(t); }
    void eqNotifyPreMerge(TNode t1, TNode t2) override
    {
      d_qee.eqNotifyPreMerge(t1, t2);
    }
    void eqNotifyPostMerge(TNode t1, TNode t2) override
    {
      d_qee.eqNotifyPostMerge(t1, t2);
    }
    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override
    {
      d_qee.eqNotifyDisequal(t1, t2, reason);
    }
  };/* class ConjectureGenerator::NotifyClass */
  /** The notify class */
  NotifyClass d_notify;
  /** (universal) equaltity engine */
  eq::EqualityEngine d_uequalityEngine;
  /** Are we in conflict */
  context::CDO<bool> d_conflict;
  /** list of redundant quantifiers in current context */
  context::CDList<Node> d_quant_red;
  /** unprocessed quantifiers in current context */
  NodeBoolMap d_quant_unproc;
  // map predicates to functions over int
  TypeNode d_intType;
  std::map< Node, Node > d_pred_to_func;
  Node getFunctionForPredicate( Node f );
  Node getFunctionAppForPredicateApp( Node n );
private:
  void conflict(TNode t1, TNode t2);
  void eqNotifyNewClass(TNode t);
  void eqNotifyPreMerge(TNode t1, TNode t2);
  void eqNotifyPostMerge(TNode t1, TNode t2);
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);
  //queries
  bool areUnivDisequalInternal( TNode n1, TNode n2 );
  bool areUnivEqualInternal( TNode n1, TNode n2 );  
  TNode getUnivRepresentativeInternal( TNode n );
public:
  QuantEqualityEngine( QuantifiersEngine * qe, context::Context* c );

  /* whether this module needs to check this round */
  bool needsCheck(Theory::Effort e) override;
  /* reset at a round */
  void reset_round(Theory::Effort e) override;
  /* Call during quantifier engine's check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /* Called for new quantifiers */
  void registerQuantifier(Node q) override;
  /** called for everything that gets asserted */
  void assertNode(Node n) override;
  /** Identify this module (for debugging, dynamic configuration, etc..) */
  std::string identify() const override { return "QuantEqualityEngine"; }
  /** queries */
  bool areUnivDisequal( TNode n1, TNode n2 );
  bool areUnivEqual( TNode n1, TNode n2 );
  TNode getUnivRepresentative( TNode n );
};


}
}
}

#endif
