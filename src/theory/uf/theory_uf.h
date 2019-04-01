/*********************                                                        */
/*! \file theory_uf.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Dejan Jovanovic, Morgan Deters
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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

#ifndef __CVC4__THEORY__UF__THEORY_UF_H
#define __CVC4__THEORY__UF__THEORY_UF_H

#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "expr/node_trie.h"
#include "theory/theory.h"
#include "theory/uf/equality_engine.h"
#include "theory/uf/symmetry_breaker.h"

namespace CVC4 {
namespace theory {
namespace uf {

class UfTermDb;
class StrongSolverTheoryUF;

class TheoryUF : public Theory {

  friend class StrongSolverTheoryUF;
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashMap<Node, Node, NodeHashFunction> NodeNodeMap;
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

  /** The associated theory strong solver (or NULL if none) */
  StrongSolverTheoryUF* d_thss;

  /** Equaltity engine */
  eq::EqualityEngine d_equalityEngine;

  /** Are we in conflict */
  context::CDO<bool> d_conflict;

  /** The conflict node */
  Node d_conflictNode;

  /** extensionality has been applied to these disequalities */
  NodeSet d_extensionality;

  /** cache of getExtensionalityDeq below */
  std::map<Node, Node> d_extensionality_deq;

  /** map from non-standard operators to their skolems */
  NodeNodeMap d_uf_std_skolem;

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

 private:  // for higher-order
  /** get extensionality disequality
   *
   * Given disequality deq f != g, this returns the disequality:
   *   (f k) != (g k) for fresh constant(s) k.
   */
  Node getExtensionalityDeq(TNode deq);

  /** applyExtensionality
   *
   * Given disequality deq f != g, if not already cached, this sends a lemma of
   * the form:
   *   f = g V (f k) != (g k) for fresh constant k.
   * on the output channel. This is an "extensionality lemma".
   * Return value is the number of lemmas of this form sent on the output
   * channel.
   */
  unsigned applyExtensionality(TNode deq);

  /**
   * Check whether extensionality should be applied for any pair of terms in the
   * equality engine.
   *
   * If we pass a null model m to this function, then we add extensionality
   * lemmas to the output channel and return the total number of lemmas added.
   * We only add lemmas for functions whose type is finite, since pairs of
   * functions whose types are infinite can be made disequal in a model by
   * witnessing a point they are disequal.
   *
   * If we pass a non-null model m to this function, then we add disequalities
   * that correspond to the conclusion of extensionality lemmas to the model's
   * equality engine. We return 0 if the equality engine of m is consistent
   * after this call, and 1 otherwise. We only add disequalities for functions
   * whose type is infinite, since our decision procedure guarantees that
   * extensionality lemmas are added for all pairs of functions whose types are
   * finite.
   */
  unsigned checkExtensionality(TheoryModel* m = nullptr);

  /** applyAppCompletion
   * This infers a correspondence between APPLY_UF and HO_APPLY
   * versions of terms for higher-order.
   * Given APPLY_UF node e.g. (f a b c), this adds the equality to its
   * HO_APPLY equivalent:
   *   (f a b c) == (@ (@ (@ f a) b) c)
   * to equality engine, if not already equal.
   * Return value is the number of equalities added.
   */
  unsigned applyAppCompletion(TNode n);

  /** check whether app-completion should be applied for any
   * pair of terms in the equality engine.
   */
  unsigned checkAppCompletion();

  /** check higher order
   * This is called at full effort and infers facts and sends lemmas
   * based on higher-order reasoning (specifically, extentionality and
   * app completion above). It returns the number of lemmas plus facts
   * added to the equality engine.
  */
  unsigned checkHigherOrder();

  /** collect model info for higher-order term
   *
   * This adds required constraints to m for term n. In particular, if n is
   * an APPLY_UF term, we add its HO_APPLY equivalent in this call. We return
   * true if the model m is consistent after this call.
   */
  bool collectModelInfoHoTerm(Node n, TheoryModel* m);

  /** get apply uf for ho apply
   * This returns the APPLY_UF equivalent for the HO_APPLY term node, where
   * node has non-functional return type (that is, it corresponds to a fully
   * applied function term).
   * This call may introduce a skolem for the head operator and send out a lemma
   * specifying the definition.
  */
  Node getApplyUfForHoApply(Node node);
  /** get the operator for this node (node should be either APPLY_UF or
   * HO_APPLY)
   */
  Node getOperatorForApplyTerm(TNode node);
  /** get the starting index of the arguments for node (node should be either
   * APPLY_UF or HO_APPLY) */
  unsigned getArgumentStartIndexForApplyTerm(TNode node);

 public:

  /** Constructs a new instance of TheoryUF w.r.t. the provided context.*/
  TheoryUF(context::Context* c, context::UserContext* u, OutputChannel& out,
           Valuation valuation, const LogicInfo& logicInfo,
           std::string instanceName = "");

  ~TheoryUF();

  void setMasterEqualityEngine(eq::EqualityEngine* eq) override;
  void finishInit() override;

  void check(Effort) override;
  Node expandDefinition(LogicRequest& logicRequest, Node node) override;
  void preRegisterTerm(TNode term) override;
  Node explain(TNode n) override;

  bool collectModelInfo(TheoryModel* m) override;

  void ppStaticLearn(TNode in, NodeBuilder<>& learned) override;
  void presolve() override;

  void addSharedTerm(TNode n) override;
  void computeCareGraph() override;

  void propagate(Effort effort) override;

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  std::string identify() const override { return "THEORY_UF"; }

  eq::EqualityEngine* getEqualityEngine() override { return &d_equalityEngine; }

  StrongSolverTheoryUF* getStrongSolver() {
    return d_thss;
  }
private:
  bool areCareDisequal(TNode x, TNode y);
  void addCarePairs(TNodeTrie* t1,
                    TNodeTrie* t2,
                    unsigned arity,
                    unsigned depth);
};/* class TheoryUF */

}/* CVC4::theory::uf namespace */
}/* CVC4::theory namespace */
}/* CVC4 namespace */

#endif /* __CVC4__THEORY__UF__THEORY_UF_H */
