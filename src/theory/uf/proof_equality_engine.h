/*********************                                                        */
/*! \file proof_equality_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
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
 * It tracks the reason for why all facts are added to an EqualityEngine in a
 * SAT-context dependent manner in a context-dependent (CDProof) object.
 *
 * It is an eager proof generator (see theory/proof_generator.h), in that
 * it stores (copies) of proofs for lemmas at the moment they are sent out.
 *
 * A theory that is proof producing and uses the equality engine may use this
 * class to manage proofs that are justified by its underlying equality engine.
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
                ProofNodeManager* pnm,
                bool pfEnabled = true,
                bool recExplain = false);
  ~ProofEqEngine() {}
  //-------------------------- assert assumption
  /** Assert predicate lit by assumption */
  bool assertAssume(TNode lit);
  //-------------------------- assert fact
  /**
   * Assert the predicate lit by proof step id, given explanation exp and
   * arguments args.
   */
  bool assertFact(Node lit,
                  PfRule id,
                  const std::vector<Node>& exp,
                  const std::vector<Node>& args);
  bool assertFact(Node lit, PfRule id, Node exp, const std::vector<Node>& args);
  /** Multi-step versions */
  bool assertFact(Node lit, Node exp, ProofStepBuffer& psb);
  bool assertFact(Node lit, Node exp, ProofGenerator* pg);
  //-------------------------- assert conflicts
  /**
   * This method is called when the equality engine of this class is
   * inconsistent (false has been proven) by a contradictory literal lit. This
   * returns the trust node corresponding to the current conflict.
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
  // TrustNode assertConflict(ProofNode* p);
  //-------------------------- assert lemma
  /**
   * Called when we have concluded conc, which is either false or a
   * disjunction.
   *
   * We provide the explanation in two parts:
   * (1) exp \ noExplain, which are literals that hold in the equality engine of
   * this class,
   * (2) noExplain, which do not necessarily hold in the equality engine of this
   * class.
   * Notice that noExplain is a subset of exp.
   *
   * The proof for conc follows from exp ^ expn by proof rule with the given
   * id and arguments.
   *
   * This call corresponds to a lemma if conc is false and expn is empty.
   *
   * This returns the TrustNode corresponding to the formula corresonding to
   * the call to this method [*], for which a proof can be provided by this
   * generator in the remainder of the user context.
   *
   * [*]
   * a. If this call does not correspond to a conflict, then this formula is:
   *   ( ^_{e in exp} <explain>(e) ^ expn ) => conc
   * where <explain>(e) is a conjunction of literals L1 ^ ... ^ Ln such that
   * L1 ^ ... ^ Ln entail e, and each Li was passed as an argument to
   * assertAssume(...) in the current SAT context. This explanation method
   * always succeeds, provided that e is a literal that currently holds in
   * the equality engine of this class. Notice that if the antecedant is empty,
   * the formula above is assumed to be conc itself. The above formula is
   * intended to be valid in Theory that owns this class.
   * b. If this call is a conflict, then this formula is:
   *   ^_{e in exp} <explain>(e)
   * The above formula is intended to be equivalent to false according to the
   * Theory that owns this class.
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
  /** Generator version */
  TrustNode assertLemma(Node conc,
                        const std::vector<Node>& exp,
                        const std::vector<Node>& noExplain,
                        ProofGenerator* pg);
  //-------------------------- explain
  TrustNode explain(Node conc);
  /** identify */
  std::string identify() const override;

 protected:
  /** Add proof step */
  bool addProofStep(Node lit,
                    PfRule id,
                    const std::vector<Node>& exp,
                    const std::vector<Node>& args);
  /** Assert internal */
  void assertFactInternal(TNode pred, bool polarity, TNode reason);
  /** assert lemma internal */
  TrustNode assertLemmaInternal(Node conc,
                                const std::vector<Node>& exp,
                                const std::vector<Node>& noExplain,
                                LazyCDProof* curr);
  /** ensure proof for fact */
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
  /** flatten and, returns the conjuncts to a */
  void flattenAnd(TNode an, std::vector<Node>& a);

 private:
  /** Reference to the equality engine */
  eq::EqualityEngine& d_ee;
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
  /**
   * Recurse explanations
   */
  bool d_recExplain;
  /** Explain
   *
   * This adds to assumps the set of facts that were asserted to this
   * class in the current SAT context by calls to assertAssume that are
   * required for showing lit.
   *
   * This additionally registers the equality proof steps required to
   * regress the explanation of lit.
   */
  void explainWithProof(Node lit, std::vector<TNode>& assumps, LazyCDProof* curr);
};

}  // namespace eq
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__PROOF_MANAGER_H */
