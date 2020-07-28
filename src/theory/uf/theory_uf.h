/*********************                                                        */
/*! \file theory_uf.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Dejan Jovanovic, Andrew Reynolds, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief This is the interface to TheoryUF implementations
 **
 ** This is the interface to TheoryUF implementations.  All
 ** implementations of TheoryUF should inherit from this class.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__THEORY_UF_H
#define CVC4__THEORY__UF__THEORY_UF_H

#include "context/cdo.h"
#include "expr/node.h"
#include "expr/node_trie.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/proof_checker.h"
#include "theory/uf/symmetry_breaker.h"
#include "theory/uf/theory_uf_rewriter.h"

namespace CVC4 {
namespace theory {
namespace uf {

class CardinalityExtension;
class HoExtension;

class TheoryUF : public Theory {

public:

  class NotifyClass : public eq::EqualityEngineNotify {
    TheoryUF& d_uf;
  public:
    NotifyClass(TheoryUF& uf): d_uf(uf) {}

    bool eqNotifyTriggerEquality(TNode equality, bool value) override
    {
      Debug("uf") << "NotifyClass::eqNotifyTriggerEquality(" << equality << ", " << (value ? "true" : "false" )<< ")" << std::endl;
      if (value) {
        return d_uf.propagate(equality);
      } else {
        // We use only literal triggers so taking not is safe
        return d_uf.propagate(equality.notNode());
      }
    }

    bool eqNotifyTriggerPredicate(TNode predicate, bool value) override
    {
      Debug("uf") << "NotifyClass::eqNotifyTriggerPredicate(" << predicate << ", " << (value ? "true" : "false") << ")" << std::endl;
      if (value) {
        return d_uf.propagate(predicate);
      } else {
       return d_uf.propagate(predicate.notNode());
      }
    }

    bool eqNotifyTriggerTermEquality(TheoryId tag,
                                     TNode t1,
                                     TNode t2,
                                     bool value) override
    {
      Debug("uf") << "NotifyClass::eqNotifyTriggerTermMerge(" << tag << ", " << t1 << ", " << t2 << ")" << std::endl;
      if (value) {
        return d_uf.propagate(t1.eqNode(t2));
      } else {
        return d_uf.propagate(t1.eqNode(t2).notNode());
      }
    }

    void eqNotifyConstantTermMerge(TNode t1, TNode t2) override
    {
      Debug("uf-notify") << "NotifyClass::eqNotifyConstantTermMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_uf.conflict(t1, t2);
    }

    void eqNotifyNewClass(TNode t) override
    {
      Debug("uf-notify") << "NotifyClass::eqNotifyNewClass(" << t << ")" << std::endl;
      d_uf.eqNotifyNewClass(t);
    }

    void eqNotifyPreMerge(TNode t1, TNode t2) override
    {
      Debug("uf-notify") << "NotifyClass::eqNotifyPreMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_uf.eqNotifyPreMerge(t1, t2);
    }

    void eqNotifyPostMerge(TNode t1, TNode t2) override
    {
      Debug("uf-notify") << "NotifyClass::eqNotifyPostMerge(" << t1 << ", " << t2 << ")" << std::endl;
      d_uf.eqNotifyPostMerge(t1, t2);
    }

    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override
    {
      Debug("uf-notify") << "NotifyClass::eqNotifyDisequal(" << t1 << ", " << t2 << ", " << reason << ")" << std::endl;
      d_uf.eqNotifyDisequal(t1, t2, reason);
    }

  };/* class TheoryUF::NotifyClass */

private:

  /** The notify class */
  NotifyClass d_notify;

  /** The associated cardinality extension (or nullptr if it does not exist) */
  std::unique_ptr<CardinalityExtension> d_thss;
  /** the higher-order solver extension (or nullptr if it does not exist) */
  std::unique_ptr<HoExtension> d_ho;

  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;

  /** Are we in conflict */
  context::CDO<bool> d_conflict;

  /** The conflict node */
  Node d_conflictNode;


  /** node for true */
  Node d_true;

  /**
   * Should be called to propagate the literal. We use a node here
   * since some of the propagated literals are not kept anywhere.
   */
  bool propagate(TNode literal);

  /**
   * Explain why this literal is true by adding assumptions
   * with proof (if "pf" is non-NULL).
   */
  void explain(TNode literal, std::vector<TNode>& assumptions, eq::EqProof* pf);

  /**
   * Explain a literal, with proof (if "pf" is non-NULL).
   */
  Node explain(TNode literal, eq::EqProof* pf);

  /** All the function terms that the theory has seen */
  context::CDList<TNode> d_functionsTerms;

  /** Symmetry analyzer */
  SymmetryBreaker d_symb;

  /** Conflict when merging two constants */
  void conflict(TNode a, TNode b);

  /** called when a new equivalance class is created */
  void eqNotifyNewClass(TNode t);

  /** called when two equivalance classes will merge */
  void eqNotifyPreMerge(TNode t1, TNode t2);

  /** called when two equivalance classes have merged */
  void eqNotifyPostMerge(TNode t1, TNode t2);

  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

 private:
  /** get the operator for this node (node should be either APPLY_UF or
   * HO_APPLY)
   */
  Node getOperatorForApplyTerm(TNode node);
  /** get the starting index of the arguments for node (node should be either
   * APPLY_UF or HO_APPLY) */
  unsigned getArgumentStartIndexForApplyTerm(TNode node);

 public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUF(context::Context* c,
           context::UserContext* u,
           OutputChannel& out,
           Valuation valuation,
           const LogicInfo& logicInfo,
           ProofNodeManager* pnm = nullptr,
           std::string instanceName = "");

  ~TheoryUF();

  TheoryRewriter* getTheoryRewriter() override { return &d_rewriter; }

  void setMasterEqualityEngine(eq::EqualityEngine* eq) override;
  void finishInit() override;

  void check(Effort) override;
  TrustNode expandDefinition(Node node) override;
  void preRegisterTerm(TNode term) override;
  TrustNode explain(TNode n) override;

  bool collectModelInfo(TheoryModel* m) override;

  void ppStaticLearn(TNode in, NodeBuilder<>& learned) override;
  void presolve() override;

  void addSharedTerm(TNode n) override;
  void computeCareGraph() override;

  void propagate(Effort effort) override;

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  std::string identify() const override { return "THEORY_UF"; }

  eq::EqualityEngine* getEqualityEngine() override { return &d_equalityEngine; }

  /** get a pointer to the uf with cardinality */
  CardinalityExtension* getCardinalityExtension() const { return d_thss.get(); }
  /** are we in conflict? */
  bool inConflict() const { return d_conflict; }

 private:
  bool areCareDisequal(TNode x, TNode y);
  void addCarePairs(TNodeTrie* t1,
                    TNodeTrie* t2,
                    unsigned arity,
                    unsigned depth);

  TheoryUfRewriter d_rewriter;
  /** Proof rule checker */
  UfProofRuleChecker d_ufProofChecker;
};/* class TheoryUF */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* CVC4__THEORY__UF__THEORY_UF_H */
