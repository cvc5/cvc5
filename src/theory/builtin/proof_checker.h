/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Builtin proof checker utility.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BUILTIN__PROOF_CHECKER_H
#define CVC5__THEORY__BUILTIN__PROOF_CHECKER_H

#include "expr/node.h"
#include "proof/method_id.h"
#include "proof/proof_checker.h"
#include "proof/proof_node.h"

namespace cvc5::internal {

class Env;

namespace theory {
namespace builtin {

/** A checker for builtin proofs */
class BuiltinProofRuleChecker : public ProofRuleChecker
{
 public:
  /** Constructor. */
  BuiltinProofRuleChecker(Env& env);
  /** Destructor. */
  ~BuiltinProofRuleChecker() {}
  /**
   * Get substitution for literal exp. Updates vars/subs to the substitution
   * specified by exp for the substitution method ids.
   */
  static bool getSubstitutionForLit(Node exp,
                                    TNode& var,
                                    TNode& subs,
                                    MethodId ids = MethodId::SB_DEFAULT);
  /**
   * Get substitution for formula exp. Adds to vars/subs to the substitution
   * specified by exp for the substitution method ids, which may be multiple
   * substitutions if exp is of kind AND and ids is SB_DEFAULT (note the other
   * substitution types always interpret applications of AND as a formula).
   * The vector "from" are the literals from exp that each substitution in
   * vars/subs are based on. For example, if exp is (and (= x t) (= y s)), then
   * vars = { x, y }, subs = { t, s }, from = { (= x y), (= y s) }.
   */
  static bool getSubstitutionFor(Node exp,
                                 std::vector<TNode>& vars,
                                 std::vector<TNode>& subs,
                                 std::vector<TNode>& from,
                                 MethodId ids = MethodId::SB_DEFAULT);

  /**
   * Apply substitution on n in skolem form. This encapsulates the exact
   * behavior of a SUBS step in a proof.
   *
   * @param n The node to substitute,
   * @param exp The (set of) equalities/literals/formulas that the substitution
   * is derived from
   * @param ids The method identifier of the substitution, by default SB_DEFAULT
   * specifying that lhs/rhs of equalities are interpreted as a substitution.
   * @param ida The method identifier of the substitution application, by
   * default SB_SEQUENTIAL specifying that substitutions are to be applied
   * sequentially
   * @return The substituted form of n.
   */
  static Node applySubstitution(Node n,
                                Node exp,
                                MethodId ids = MethodId::SB_DEFAULT,
                                MethodId ida = MethodId::SBA_SEQUENTIAL);
  static Node applySubstitution(Node n,
                                const std::vector<Node>& exp,
                                MethodId ids = MethodId::SB_DEFAULT,
                                MethodId ida = MethodId::SBA_SEQUENTIAL);
  /** Apply substitution + rewriting
   *
   * Combines the above two steps.
   *
   * @param n The node to substitute and rewrite,
   * @param exp The (set of) equalities corresponding to the substitution
   * @param ids The method identifier of the substitution.
   * @param ida The method identifier of the substitution application.
   * @param idr The method identifier of the rewriter.
   * @return The substituted, rewritten form of n.
   */
  Node applySubstitutionRewrite(Node n,
                                const std::vector<Node>& exp,
                                MethodId ids = MethodId::SB_DEFAULT,
                                MethodId ida = MethodId::SBA_SEQUENTIAL,
                                MethodId idr = MethodId::RW_REWRITE);

  /** get a TheoryId from a node, return false if we fail */
  static bool getTheoryId(TNode n, TheoryId& tid);
  /** Make a TheoryId into a node */
  static Node mkTheoryIdNode(TheoryId tid);

  /** Register all rules owned by this rule checker into pc. */
  void registerTo(ProofChecker* pc) override;
 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;

 private:
  /** Reference to the environment. */
  Env& d_env;
  /** Pointer to the rewrite database */
  rewriter::RewriteDb* d_rdb;
};

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__PROOF_CHECKER_H */
