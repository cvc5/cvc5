/*********************                                                        */
/*! \file proof_equality_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The proof-producing equality engine
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__PROOF_EQUALITY_ENGINE_H
#define CVC4__THEORY__UF__PROOF_EQUALITY_ENGINE_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "expr/lazy_proof.h"
#include "expr/node.h"
#include "expr/proof_node.h"
#include "expr/proof_node_manager.h"
#include "expr/proof_step_buffer.h"
#include "theory/eager_proof_generator.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace eq {

/**
 * A layer on top of an EqualityEngine. The goal of this class is manage the
 * use of an EqualityEngine object in such a way that the proper proofs are
 * internally constructed, and can be retrieved from this class when
 * necessary.
 *
 * Notice that this class is intended to be a *partial layer* on top of
 * equality engine. A user of this class should still issue low-level calls
 * (getRepresentative, areEqual, areDisequal, etc.) on the underlying equality
 * engine directly. The methods that should *not* be called directly on the
 * underlying equality engine are:
 * - assertEquality/assertPredicate [*]
 * - explain
 * Instead, the user should use variants of the above methods provided by
 * the public interface of this class.
 *
 * [*] the exception is that assertions from the fact queue (who are their own
 * explanation) should be sent directly to the underlying equality engine. This
 * is for the sake of efficiency.
 *
 * This class tracks the reason for why all facts are added to an EqualityEngine
 * in a SAT-context dependent manner in a context-dependent (CDProof) object.
 * It furthermore maintains an internal FactProofGenerator class for managing
 * proofs of facts whose steps are explicitly provided (those that are given
 * concrete PfRule, children, and args). Call these "simple facts".
 *
 * Overall, this class is an eager proof generator (theory/proof_generator.h),
 * in that it stores (copies) of proofs for lemmas at the moment they are sent
 * out.
 *
 * A theory that is proof producing and uses the equality engine may use this
 * class to manage proofs that are justified by its underlying equality engine.
 * In particular, the following interfaces are available for constructing
 * a TrustNode:
 * - assertConflict, when the user of the equality engine has discovered that
 * false can be derived from the current state,
 * - assertLemma, for lemmas/conflicts that can be (partially) explained in the
 * current state,
 * - explain, for explaining why a literal is true in the current state.
 * Details on these methods can be found below.
 */
class ProofEqEngine : public EagerProofGenerator
{
  typedef context::CDHashSet<Node, NodeHashFunction> NodeSet;
  typedef context::CDHashMap<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      NodeProofMap;

 public:
  ProofEqEngine(context::Context* c,
                context::UserContext* u,
                EqualityEngine& ee,
                ProofNodeManager* pnm);
  ~ProofEqEngine() {}
  //-------------------------- assert assumption
  /**
   * Assert literal lit by assumption to the underlying equality engine. It is
   * its own explanation.
   *
   * @param lit The literal to assert to the equality engine
   * @return true if this fact was processed by this method. If lit already
   * holds in the equality engine, this method returns false.
   */
  bool assertAssume(TNode lit);
  //-------------------------- assert fact
  /**
   * Assert the literal lit by proof step id, given explanation exp and
   * arguments args. This fact is
   *
   * @param lit The literal to assert to the equality engine
   * @param id The proof rule of the proof step concluding lit
   * @param exp The premises of the proof step concluding lit. These are also
   * the premises that are used when calling explain(lit).
   * @param args The arguments to the proof step concluding lit.
   * @return true if this fact was processed by this method. If lit already
   * holds in the equality engine, this method returns false.
   */
  bool assertFact(Node lit,
                  PfRule id,
                  const std::vector<Node>& exp,
                  const std::vector<Node>& args);
  /** Same as above but where exp is (conjunctive) node */
  bool assertFact(Node lit, PfRule id, Node exp, const std::vector<Node>& args);
  /**
   * Multi-step version of assert fact via a proof step buffer. This method
   * is similar to above, but the justification for lit may have multiple steps.
   * In particular, we assume that psb has a list of proof steps where the
   * proof step concluding lit has free assumptions exp.
   *
   * For example, a legal call to this method is such that:
   *   lit: A
   *   exp: B
   *   psb.d_steps: { A by (step id1 {B,C} {}), C by (step id2 {} {}) )
   * In other words, A holds by a proof step with rule id1 and premises
   * B and C, and C holds by proof step with rule id2 and no premises.
   *
   * @param lit The literal to assert to the equality engine.
   * @param exp The premises of the proof steps concluding lit. These are also
   * the premises that are used when calling explain(lit).
   * @param psb The proof step buffer containing the proof steps.
   * @return true if this fact was processed by this method. If lit already
   * holds in the equality engine, this method returns false.
   */
  bool assertFact(Node lit, Node exp, ProofStepBuffer& psb);
  /**
   * Assert fact via generator pg. This method asserts lit with explanation exp
   * to the equality engine of this class. It must be the case that pg can
   * provide a proof for lit in terms of exp. More precisely, pg should be
   * prepared in the remainder of the SAT context to respond to a call to
   * ProofGenerator::getProofFor(lit), and return a proof whose free
   * assumptions are a subset of the conjuncts of exp.
   *
   * @param lit The literal to assert to the equality engine.
   * @param exp The premises of the proof concluding lit. These are also
   * the premises that are used when calling explain(lit).
   * @param pg The proof generator that can provide a proof concluding lit
   * from free asumptions in exp.
   * @return true if this fact was processed by this method. If lit already
   * holds in the equality engine, this method returns false.
   */
  bool assertFact(Node lit, Node exp, ProofGenerator* pg);
  //-------------------------- assert conflicts
  /**
   * This method is called when the equality engine of this class is
   * inconsistent (false has been proven) by a contradictory literal lit. This
   * returns the trust node corresponding to the current conflict.
   *
   * @param lit The conflicting literal, which must rewrite to false.
   * @return The trust node capturing the fact that this class can provide a
   * proof for this conflict.
   */
  TrustNode assertConflict(Node lit);
  /**
   * Get proven conflict from contradictory facts. This method is called when
   * the proof rule with premises exp and arguments args implies a contradiction
   * by proof rule id.
   *
   * This method returns the TrustNode containing the corresponding conflict
   * resulting from adding this step, and ensures that a proof has been stored
   * internally so that this class may respond to a call to
   * ProofGenerator::getProof(...).
   */
  TrustNode assertConflict(PfRule id,
                           const std::vector<Node>& exp,
                           const std::vector<Node>& args);
  /** Multi-step version */
  TrustNode assertConflict(const std::vector<Node>& exp, ProofStepBuffer& psb);
  //-------------------------- assert lemma
  /**
   * Called when we have concluded conc, typically via theory specific
   * reasoning. The purpose of this method is to construct a TrustNode of
   * kind TrustNodeKind::LEMMA or TrustNodeKind::CONFLICT corresponding to the
   * lemma or conflict to be sent on the output channel of the Theory.
   *
   * The user provides the explanation of conc in two parts:
   * (1) (exp \ noExplain), which are literals that hold in the equality engine
   * of this class,
   * (2) noExplain, which do not necessarily hold in the equality engine of this
   * class.
   * Notice that noExplain is a subset of exp.
   *
   * The proof for conc follows from exp by proof rule with the given
   * id and arguments.
   *
   * This call corresponds to a conflict if conc is false and noExplain is
   * empty.
   *
   * This returns the TrustNode corresponding to the formula corresonding to
   * the call to this method [*], for which a proof can be provided by this
   * generator in the remainder of the user context.
   *
   * [*]
   * a. If this call does not correspond to a conflict, then this formula is:
   *   ( ^_{e in exp \ noExplain} <explain>(e) ^ noExplain ) => conc
   * where <explain>(e) is a conjunction of literals L1 ^ ... ^ Ln such that
   * L1 ^ ... ^ Ln entail e, and each Li was passed as an explanation to a
   * call to assertFact in the current SAT context. This explanation method
   * always succeeds, provided that e is a literal that currently holds in
   * the equality engine of this class. Notice that if the antecedant is empty,
   * the formula above is assumed to be conc itself. The above formula is
   * intended to be valid in Theory that owns this class.
   * b. If this call is a conflict, then this formula is:
   *   ^_{e in exp} <explain>(e)
   * The formula can be queried via TrustNode::getProven in the standard way.
   */
  TrustNode assertLemma(Node conc,
                        PfRule id,
                        const std::vector<Node>& exp,
                        const std::vector<Node>& noExplain,
                        const std::vector<Node>& args);
  /** Multi-step version */
  TrustNode assertLemma(Node conc,
                        const std::vector<Node>& exp,
                        const std::vector<Node>& noExplain,
                        ProofStepBuffer& psb);
  /** Generator version, where pg has a proof of conc */
  TrustNode assertLemma(Node conc,
                        const std::vector<Node>& exp,
                        const std::vector<Node>& noExplain,
                        ProofGenerator* pg);
  //-------------------------- explain
  /**
   * Explain literal conc. This calls the appropriate methods in the underlying
   * equality engine of this class to construct the explanation of why conc
   * currently holds.
   *
   * It returns a trust node of kind TrustNodeKind::PROP_EXP whose node
   * is the explanation of conc (a conjunction of literals that implies it).
   * The proof that can be proven by this generator is then (=> exp conc), see
   * TrustNode::getPropExpProven(conc,exp);
   *
   * @param conc The conclusion to explain
   * @return The trust node indicating the explanation of conc and the generator
   * (this class) that can prove the implication.
   */
  TrustNode explain(Node conc);

 private:
  /**
   * The default proof generator (for simple facts). This class is a context
   * dependent mapping from formulas to proof steps. It does not generate
   * ProofNode until it is asked to provide a proof for a given fact.
   */
  class FactProofGenerator : public ProofGenerator
  {
    typedef context::
        CDHashMap<Node, std::shared_ptr<ProofStep>, NodeHashFunction>
            NodeProofStepMap;

   public:
    FactProofGenerator(context::Context* c, ProofNodeManager* pnm);
    ~FactProofGenerator() {}
    /** add step */
    bool addStep(Node fact, ProofStep ps);
    /** Get proof for */
    std::shared_ptr<ProofNode> getProofFor(Node f) override;
    /** identify */
    std::string identify() const override { return "FactProofGenerator"; }

   private:
    /** maps expected to ProofStep */
    NodeProofStepMap d_facts;
    /** the proof node manager */
    ProofNodeManager* d_pnm;
  };
  /** Assert internal */
  bool assertFactInternal(TNode pred, bool polarity, TNode reason);
  /** holds */
  bool holds(TNode pred, bool polarity);
  /**
   * Assert lemma internal. This method is called for ensuring the proof of
   * conc exists in curr, where exp / noExplain are the its explanation (see
   * assertLemma). This method is used for conflicts as well, where noExplain
   * must be empty and conc = d_false.
   *
   * If curr is null, no proof is constructed.
   *
   * This method returns the trust node of the lemma or conflict with this
   * class as the proof generator.
   */
  TrustNode assertLemmaInternal(Node conc,
                                const std::vector<Node>& exp,
                                const std::vector<Node>& noExplain,
                                LazyCDProof* curr);
  /**
   * Ensure proof for fact. This is called by the above method after we have
   * determined the final set of assumptions used for showing conc. This
   * method is used for lemmas, conflicts, and explanations for propagations.
   * The argument tnk is the kind of trust node to return.
   */
  TrustNode ensureProofForFact(Node conc,
                               const std::vector<TNode>& assumps,
                               TrustNodeKind tnk,
                               LazyCDProof* curr);
  /**
   * Make the conjunction of nodes in a. Returns true if a is empty, and a
   * single literal if a has size 1.
   */
  Node mkAnd(const std::vector<Node>& a);
  Node mkAnd(const std::vector<TNode>& a);
  /** Reference to the equality engine */
  eq::EqualityEngine& d_ee;
  /** The default proof generator (for simple facts) */
  FactProofGenerator d_factPg;
  /** common nodes */
  Node d_true;
  Node d_false;
  /** the proof node manager */
  ProofNodeManager* d_pnm;
  /** The SAT-context-dependent proof object */
  LazyCDProof d_proof;
  /**
   * The keep set of this class. This set is maintained to ensure that
   * facts and their explanations are reference counted. Since facts and their
   * explanations are SAT-context-dependent, this set is also
   * SAT-context-dependent.
   */
  NodeSet d_keep;
  /**
   * Whether proofs are enabled. If this flag is false, then this class acts
   * as a simplified interface to the EqualityEngine, without proofs.
   */
  bool d_pfEnabled;
  /** Explain
   *
   * This adds to assumps the set of facts that were asserted to this
   * class in the current SAT context by calls to assertAssume that are
   * required for showing lit.
   *
   * This additionally registers the equality proof steps required to
   * regress the explanation of lit.
   */
  void explainWithProof(Node lit,
                        std::vector<TNode>& assumps,
                        LazyCDProof* curr);
};

}  // namespace eq
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__PROOF_MANAGER_H */
