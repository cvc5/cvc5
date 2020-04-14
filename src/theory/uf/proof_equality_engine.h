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
#include "expr/node.h"
#include "expr/proof.h"
#include "expr/proof_node.h"
#include "expr/proof_node_manager.h"
#include "theory/proof_output_channel.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace eq {

/**
 * A proof-producing equality engine.
 *
 * This is a layer on top of an EqualityEngine. It tracks the reason for why all
 * facts are added to an EqualityEngine in a SAT-context dependent manner in a
 * context-dependent (CDProof) object. The proof of certain facts can be asked
 * via the getProof interface.
 */
class ProofEqEngine : public EagerProofGenerator
{
  typedef context::CDHashMap<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      NodeProofMap;

 public:
  ProofEqEngine(context::Context* c, EqualityEngine& ee, ProofNodeManager* pnm);
  ~ProofEqEngine() {}

  /** Get the proof for lemma lem */
  std::shared_ptr<ProofNode> getProof(Node lem) override;

  /** Assert the predicate by proof step id, given explanation exp */
  Node assertLit(Node lit, ProofStep id, const std::vector<Node>& exp);
  /** Assert predicate by assumption */
  Node assertLitAssume(Node lit);
  /** Assert (dis)equality by substitution + rewriting, given explanation exp */
  Node assertEqSubsRewrite(Node lit, const std::vector<Node>& exp);

  /** Explain
   *
   * This adds to assertions the set of assertions that were asserted to this
   * class in the current SAT context by calls to assertAssume that are
   * required for showing lit.
   *
   * This additionally registers the equality proof steps required to
   * regress the explanation of lit.
   */
  void explain(Node lit, std::vector<TNode>& assertions);

 protected:
  /** TODO: necessary?
   * Get proof for fact lit, or nullptr if it does not exist. It must be the
   * case that lit was passed as the first argument to either a variant of
   * assertLit or explain.
   */
  std::shared_ptr<ProofNode> getProofForFact(Node lit) const;
  /** Assert internal */
  void assertInternal(Node pred, bool polarity, TNode reason);
  // ----------------------- common proof utilities
  /**
   * The following functions ensure that a proof step is registered for
   * an equality of a common form.
   *
   * They return the equality that is proven by the proof step, or Node::null()
   * if the proof step was invalid.
   *
   * Each of these functions may take:
   * - Terms, denoted a,b, which in part determine the conclusion of the
   * given proof step.
   * - Assumptions, denoted exp, eq1, eq2, which are premisesrequired to derive
   * the conclusion.
   *
   * If ensureChildren is true, then it must be the case that proofs have been
   * registered for each equality in the assumption.
   */
  /**
   * Ensure ASSUME(F), which proves F, has been registed as a proof step
   */
  Node pfAssume(Node f);
  /**
   * Ensure REFL(a), which proves a = a, has been registed as a proof step.
   */
  Node pfRefl(Node a);
  /**
   * Ensure REWRITE(a), which proves a = rewrite(a) has been registed as a proof
   * step.
   */
  Node pfRewrite(Node a);
  /**
   * TODO
   * Ensure false has been registed as a proof step, where rewrite(eq) = false.
   */
  Node pfRewriteFalse(Node eq, bool ensureChildren = false);
  /**
   * Ensure SUBS(P[exp], a), which proves a = a.substitute^*(exp), has been
   * registered as a proof step.
   */
  Node pfSubs(Node a,
              const std::vector<Node>& exp,
              bool ensureChildren = false);
  /**
   * Ensure REWRITE(SUBS(P[exp], a)), which proves
   *   a = rewrite(a.subsitute^*(exp))
   * has been registered as a proof step.
   */
  Node pfSubsRewrite(Node a,
                     const std::vector<Node>& exp,
                     bool ensureChildren = false);
  /**
   * Ensure that:
   *   TRANS(REWRITE(SUBS(P[exp], a)),SYMM(REWRITE(SUBS(P[exp], b))))
   * which proves:
   *   a = rewrite(a.substitute^*(exp)) = rewrite(b.substitute^*(exp)) = b
   * has been registered as a proof step.
   */
  Node pfEqualBySubsRewrite(Node a,
                            Node b,
                            const std::vector<Node>& exp,
                            bool ensureChildren = false);
  /**
   * TODO
   * Ensure that:
   *   a = rewrite(a.substitute^*(exp)) != rewrite(b.substitute^*(exp)) = b
   * has been registered as a proof step.
   */
  Node pfDisequalBySubsRewrite(Node a,
                               Node b,
                               const std::vector<Node>& exp,
                               bool ensureChildren = false);
  /**
   * Ensure that TRANS(P[eq1], P[eq2]), which proves:
   *    eq1[0] = eq1[1] == eq2[0] = eq2[1]
   * has been registered as a proof step. It must be the case that eq1[1] is
   * the same as eq2[0].
   */
  Node pfTrans(Node eq1, Node eq2, bool ensureChildren = false);
  /**
   * Ensure that SYMM(P[eq]), which proves eq[1] = eq[0], has been registered as
   * a proof step.
   */
  Node pfSymm(Node eq, bool ensureChildren = false);
  // ----------------------- end standard proofs
  /**
   * Make the conjunction of nodes in a. Returns true if a is empty, and a
   * single literal if a has size 1.
   */
  Node mkAnd(const std::vector<Node>& a);

 private:
  /** Reference to the equality engine */
  eq::EqualityEngine& d_ee;
  /** common nodes */
  Node d_true;
  /** The proof */
  CDProof d_proof;
  /** Whether proofs are enabled */
  bool d_proofsEnabled;
};

}  // namespace eq
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__PROOF_MANAGER_H */
