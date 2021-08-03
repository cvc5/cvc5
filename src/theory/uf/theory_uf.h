/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Morgan Deters, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * This is the interface to TheoryUF implementations
 *
 * All implementations of TheoryUF should inherit from this class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__UF__THEORY_UF_H
#define CVC5__THEORY__UF__THEORY_UF_H

#include "expr/node.h"
#include "expr/node_trie.h"
#include "theory/theory.h"
#include "theory/theory_eq_notify.h"
#include "theory/theory_state.h"
#include "theory/uf/proof_checker.h"
#include "theory/uf/symmetry_breaker.h"
#include "theory/uf/theory_uf_rewriter.h"

namespace cvc5 {
namespace theory {
namespace uf {

class CardinalityExtension;
class HoExtension;

class TheoryUF : public Theory {
 public:
  class NotifyClass : public TheoryEqNotifyClass
  {
   public:
    NotifyClass(TheoryInferenceManager& im, TheoryUF& uf)
        : TheoryEqNotifyClass(im), d_uf(uf)
    {
    }

    void eqNotifyNewClass(TNode t) override
    {
      Debug("uf-notify") << "NotifyClass::eqNotifyNewClass(" << t << ")"
                         << std::endl;
      d_uf.eqNotifyNewClass(t);
    }

    void eqNotifyMerge(TNode t1, TNode t2) override
    {
      Debug("uf-notify") << "NotifyClass::eqNotifyMerge(" << t1 << ", " << t2
                         << ")" << std::endl;
      d_uf.eqNotifyMerge(t1, t2);
    }

    void eqNotifyDisequal(TNode t1, TNode t2, TNode reason) override
    {
      Debug("uf-notify") << "NotifyClass::eqNotifyDisequal(" << t1 << ", " << t2 << ", " << reason << ")" << std::endl;
      d_uf.eqNotifyDisequal(t1, t2, reason);
    }

   private:
    /** Reference to the parent theory */
    TheoryUF& d_uf;
  };/* class TheoryUF::NotifyClass */

private:
  /** The associated cardinality extension (or nullptr if it does not exist) */
  std::unique_ptr<CardinalityExtension> d_thss;
  /** the higher-order solver extension (or nullptr if it does not exist) */
  std::unique_ptr<HoExtension> d_ho;

  /** node for true */
  Node d_true;

  /** All the function terms that the theory has seen */
  context::CDList<TNode> d_functionsTerms;

  /** Symmetry analyzer */
  SymmetryBreaker d_symb;

  /** called when a new equivalance class is created */
  void eqNotifyNewClass(TNode t);

  /** called when two equivalance classes have merged */
  void eqNotifyMerge(TNode t1, TNode t2);

  /** called when two equivalence classes are made disequal */
  void eqNotifyDisequal(TNode t1, TNode t2, TNode reason);

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

  //--------------------------------- initialization
  /** get the official theory rewriter of this theory */
  TheoryRewriter* getTheoryRewriter() override;
  /** get the proof checker of this theory */
  ProofRuleChecker* getProofChecker() override;
  /**
   * Returns true if we need an equality engine. If so, we initialize the
   * information regarding how it should be setup. For details, see the
   * documentation in Theory::needsEqualityEngine.
   */
  bool needsEqualityEngine(EeSetupInfo& esi) override;
  /** finish initialization */
  void finishInit() override;
  //--------------------------------- end initialization

  //--------------------------------- standard check
  /** Do we need a check call at last call effort? */
  bool needsCheckLastEffort() override;
  /** Post-check, called after the fact queue of the theory is processed. */
  void postCheck(Effort level) override;
  /** Notify fact */
  void notifyFact(TNode atom, bool pol, TNode fact, bool isInternal) override;
  //--------------------------------- end standard check

  /** Collect model values in m based on the relevant terms given by termSet */
  bool collectModelValues(TheoryModel* m,
                          const std::set<Node>& termSet) override;

  TrustNode ppRewrite(TNode node, std::vector<SkolemLemma>& lems) override;
  void preRegisterTerm(TNode term) override;
  TrustNode explain(TNode n) override;

  void ppStaticLearn(TNode in, NodeBuilder& learned) override;
  void presolve() override;

  void computeCareGraph() override;

  EqualityStatus getEqualityStatus(TNode a, TNode b) override;

  std::string identify() const override { return "THEORY_UF"; }
 private:
  /** Explain why this literal is true by building an explanation */
  void explain(TNode literal, Node& exp);

  bool areCareDisequal(TNode x, TNode y);
  void addCarePairs(const TNodeTrie* t1,
                    const TNodeTrie* t2,
                    unsigned arity,
                    unsigned depth);
  /**
   * Is t a higher order type? A higher-order type is a function type having
   * an argument type that is also a function type. This is used for checking
   * logic exceptions.
   */
  bool isHigherOrderType(TypeNode tn);
  TheoryUfRewriter d_rewriter;
  /** Proof rule checker */
  UfProofRuleChecker d_checker;
  /** A (default) theory state object */
  TheoryState d_state;
  /** A (default) inference manager */
  TheoryInferenceManager d_im;
  /** The notify class */
  NotifyClass d_notify;
  /** Cache for isHigherOrderType */
  std::map<TypeNode, bool> d_isHoType;
};/* class TheoryUF */

}  // namespace uf
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__UF__THEORY_UF_H */
