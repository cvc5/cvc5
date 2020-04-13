/*********************                                                        */
/*! \file equality_proof_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Equality proof manager utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__UF__EQUALITY_PROOF_MANAGER_H
#define CVC4__THEORY__UF__EQUALITY_PROOF_MANAGER_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "expr/proof.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"
#include "theory/uf/equality_engine.h"

namespace CVC4 {
namespace theory {
namespace eq {

/**
 * A proof manager for strings.
 *
 * This is intended to be run as a layer on top of an EqualityEngine. It tracks
 * the reason for why all facts are added to an EqualityEngine in a SAT-context
 * depnendent manner in a context-dependent (CDProof) object.
 */
class EqProofManager
{
  typedef context::CDHashMap<Node, std::shared_ptr<ProofNode>, NodeHashFunction>
      NodeProofMap;

 public:
  EqProofManager(context::Context* c, EqualityEngine& ee, ProofChecker* pc);
  ~EqProofManager() {}
  /** Get proof for fact, or nullptr if it does not exist */
  std::shared_ptr<ProofNode> getProof(Node fact) const;

  /** Assert predicate or (dis)equality by assumption */
  Node assertAssume(Node lit);
  /** Assert (dis)equality by substitution + rewriting */
  Node assertEqualitySubsRewrite(Node lit, const std::vector<Node>& exp);

 protected:
  // ----------------------- standard proofs
  /**
   * The following functions ensure that a proof object is constructed for
   * an equality of a given form.
   *
   * They return the equality that is proven by the proof step, or Node::null()
   * if the proof step was invalid.
   *
   * Each of these functions may take:
   * - Terms, denoted a,b, which in part determine the conclusion of the
   * given proof step.
   * - Assumptions, denoted exp, eq1, eq2, which are required to derive the
   * conclusion.
   *
   * If ensureChildren is true, then it must be the case that proofs have been
   * registered for each equality in the assumption.
   */
  /**
   * Ensure formula F has been registed as an assumption
   */
  Node pfAssume(Node f);
  /**
   * Ensure a = a has been registed as a proof step.
   */
  Node pfRefl(Node a);
  /**
   * Ensure a = rewrite(a) has been registed as a proof step.
   */
  Node pfRewrite(Node a);
  /**
   * Ensure false has been registed as a proof step, where rewrite(eq) = false.
   */
  Node pfRewriteFalse(Node eq, bool ensureChildren = false);
  /**
   * Ensure a = a.substitute^*(exp) has been registered as a proof step.
   */
  Node pfSubs(Node a,
              const std::vector<Node>& exp,
              bool ensureChildren = false);
  /**
   * Ensure a = rewrite(a.subsitute^*(exp)) has been registered as a proof step.
   */
  Node pfSubsRewrite(Node a,
                     const std::vector<Node>& exp,
                     bool ensureChildren = false);
  /**
   * Ensure that:
   *   a = rewrite(a.substitute^*(exp)) = rewrite(b.substitute^*(exp)) = b
   * has been registered as a proof step.
   */
  Node pfEqualBySubsRewrite(Node a,
                            Node b,
                            const std::vector<Node>& exp,
                            bool ensureChildren = false);
  /**
   * Ensure that:
   *   a = rewrite(a.substitute^*(exp)) != rewrite(b.substitute^*(exp)) = b
   * has been registered as a proof step.
   */
  Node pfDisequalBySubsRewrite(Node a,
                               Node b,
                               const std::vector<Node>& exp,
                               bool ensureChildren = false);
  /**
   * Ensure that eq1[0] = eq1[1] == eq2[0] = eq2[1] has been registered as a
   * proof step.
   */
  Node pfTrans(Node eq1, Node eq2, bool ensureChildren = false);
  /**
   * Ensure that eq[1] = eq[0] has been registered as a proof step.
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
  /** The proof checker */
  ProofChecker* d_checker;
  /** common nodes */
  Node d_true;
  /** The proof */
  CDProof d_proof;
};

}  // namespace eq
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__STRINGS__PROOF_MANAGER_H */
