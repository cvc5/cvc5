/*********************                                                        */
/*! \file proof_checker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Equality proof checker utility
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__BUILTIN__PROOF_CHECKER_H
#define CVC4__THEORY__BUILTIN__PROOF_CHECKER_H

#include "expr/node.h"
#include "expr/proof_checker.h"
#include "expr/proof_node.h"

namespace CVC4 {
namespace theory {

/** Identifiers for rewriters.
 *
 * A "rewriter" is abstractly a method from Node to Node, where the output
 * is semantically equivalent to the input. The identifiers below list
 * various methods that have this contract. This identifier is used
 * in a number of the builtin rules.
 */
enum class RewriterId : uint32_t
{
  // Rewriter::rewrite(n)
  REWRITE,
  // Rewriter::rewriteExtEquality(n)
  REWRITE_EQ_EXT,
  // identity
  IDENTITY,
};
/** Converts a rewriter id to a string. */
const char* toString(RewriterId id);
/** Write a rewriter id to out */
std::ostream& operator<<(std::ostream& out, RewriterId id);

namespace builtin {

/** A checker for builtin proofs */
class BuiltinProofRuleChecker : public ProofRuleChecker
{
 public:
  BuiltinProofRuleChecker() {}
  ~BuiltinProofRuleChecker() {}
  /**
   * Apply rewrite on n (in witness form). This encapsulates the exact behavior
   * of a REWRITE step in a proof. Rewriting is performed on the Skolem form of
   * n.
   *
   * @param n The node (in witness form) to rewrite,
   * @param id The identifier of the rewriter.
   * @return The rewritten form of n.
   */
  static Node applyRewrite(Node n, RewriterId id = RewriterId::REWRITE);
  /**
   * Apply substitution on n (in witness form). This encapsulates the exact
   * behavior of a SUBS step in a proof. Substitution is on the Skolem form of
   * n.
   *
   * @param n The node (in witness form) to substitute,
   * @param exp The (set of) equalities (in witness form) corresponding to the
   * substitution
   * @return The substituted form of n.
   */
  static Node applySubstitution(Node n, Node exp);
  static Node applySubstitution(Node n, const std::vector<Node>& exp);
  /** Apply substitution + rewriting
   *
   * Combines the above two steps.
   *
   * @param n The node (in witness form) to substitute and rewrite,
   * @param exp The (set of) equalities (in witness form) corresponding to the
   * substitution
   * @param id The identifier of the rewriter.
   * @return The substituted, rewritten form of n.
   */
  static Node applySubstitutionRewrite(Node n,
                                       const std::vector<Node>& exp,
                                       RewriterId id = RewriterId::REWRITE);
  /** get a rewriter Id from a node, return false if we fail */
  static bool getRewriterId(TNode n, RewriterId& i);
  /** Make a rewriter id node */
  static Node mkRewriterId(RewriterId i);

  /** Register all rules owned by this rule checker into pc. */
  void registerTo(ProofChecker* pc) override;

 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
  /**
   * Apply rewrite (on Skolem form). id is the identifier of the rewriter.
   */
  static Node applyRewriteExternal(Node n, RewriterId id = RewriterId::REWRITE);
  /**
   * Apply substitution for n (on Skolem form), where exp is an equality
   * (or set of equalities) in Witness form. Returns the result of
   * n * { exp[0] -> exp[1] } in Skolem form.
   */
  static Node applySubstitutionExternal(Node n, Node exp);
  static Node applySubstitutionExternal(Node n, const std::vector<Node>& exp);
};

}  // namespace builtin
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BUILTIN__PROOF_CHECKER_H */
