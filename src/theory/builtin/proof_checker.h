/*********************                                                        */
/*! \file proof_checker.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
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

/** 
 * Identifiers for rewriters and substitutions, which we abstractly
 * classify as "methods".  Methods have a unique identifier in the internal
 * proof calculus implemented by the checker below.
 *
 * A "rewriter" is abstractly a method from Node to Node, where the output
 * is semantically equivalent to the input. The identifiers below list
 * various methods that have this contract. This identifier is used
 * in a number of the builtin rules.
 *
 * A substitution is a method for turning a formula into a substitution.
 */
enum class MethodId : uint32_t
{
  //---------------------------- Rewriters
  // Rewriter::rewrite(n)
  RW_REWRITE,
  // identity
  RW_IDENTITY,
  //---------------------------- Substitutions
  // (= x y) is interpreted as x -> y, using Node::substitute
  SB_DEFAULT,
  // P, (not P) are interpreted as P -> true, P -> false using Node::substitute
  SB_LITERAL,
  // P is interpreted as P -> true using Node::substitute
  SB_FORMULA,
};
/** Converts a rewriter id to a string. */
const char* toString(MethodId id);
/** Write a rewriter id to out */
std::ostream& operator<<(std::ostream& out, MethodId id);
/** Make a method id node */
Node mkMethodId(MethodId id);

namespace builtin {

/** A checker for builtin proofs */
class BuiltinProofRuleChecker : public ProofRuleChecker
{
 public:
  BuiltinProofRuleChecker() {}
  ~BuiltinProofRuleChecker() {}
  /**
   * Apply rewrite on n (in skolem form). This encapsulates the exact behavior
   * of a REWRITE step in a proof.
   *
   * @param n The node to rewrite,
   * @param idr The method identifier of the rewriter, by default RW_REWRITE
   * specifying a call to Rewriter::rewrite.
   * @return The rewritten form of n.
   */
  static Node applyRewrite(Node n, MethodId idr = MethodId::RW_REWRITE);
  /**
   * Get substitution. Updates vars/subs to the substitution specified by
   * exp (e.g. as an equality) for the substitution method ids.
   */
  static bool getSubstitution(Node exp,
                              TNode& var,
                              TNode& subs,
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
   * @return The substituted form of n.
   */
  static Node applySubstitution(Node n,
                                Node exp,
                                MethodId ids = MethodId::SB_DEFAULT);
  static Node applySubstitution(Node n,
                                const std::vector<Node>& exp,
                                MethodId ids = MethodId::SB_DEFAULT);
  /** Apply substitution + rewriting
   *
   * Combines the above two steps.
   *
   * @param n The node to substitute and rewrite,
   * @param exp The (set of) equalities corresponding to the substitution
   * @param ids The method identifier of the substitution.
   * @param idr The method identifier of the rewriter.
   * @return The substituted, rewritten form of n.
   */
  static Node applySubstitutionRewrite(Node n,
                                       const std::vector<Node>& exp,
                                       MethodId ids = MethodId::SB_DEFAULT,
                                       MethodId idr = MethodId::RW_REWRITE);
  /** get a method identifier from a node, return false if we fail */
  static bool getMethodId(TNode n, MethodId& i);
  /**
   * Get method identifiers from args starting at the given index. Store their
   * values into ids, idr. This method returns false if args does not contain
   * valid method identifiers at position index in args.
   */
  bool getMethodIds(const std::vector<Node>& args,
                    MethodId& ids,
                    MethodId& idr,
                    size_t index);
  /**
   * Add method identifiers ids and idr as nodes to args. This does not add ids
   * or idr if their values are the default ones.
   */
  static void addMethodIds(std::vector<Node>& args, MethodId ids, MethodId idr);

  /** Register all rules owned by this rule checker into pc. */
  void registerTo(ProofChecker* pc) override;
 protected:
  /** Return the conclusion of the given proof step, or null if it is invalid */
  Node checkInternal(PfRule id,
                     const std::vector<Node>& children,
                     const std::vector<Node>& args) override;
};

}  // namespace builtin
}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__BUILTIN__PROOF_CHECKER_H */
