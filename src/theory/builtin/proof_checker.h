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
namespace builtin {

/** A checker for builtin proofs */
class BuiltinProofRuleChecker : public ProofRuleChecker
{
 public:
  BuiltinProofRuleChecker() {}
  ~BuiltinProofRuleChecker() {}
  /**
   * Apply rewrite. This encapsulates the exact behavior of a REWRITE step
   * in a proof.
   */
  static Node applyRewrite(Node n, uint32_t index = 0);
  /**
   * Apply substitution. This encapsulates the exact behavior of a SUBS step
   * in a proof.
   */
  static Node applySubstitution(Node n, Node exp);
  static Node applySubstitution(Node n, const std::vector<Node>& exp);
  /** Apply substitution + rewriting */
  static Node applySubstitutionRewrite(Node n, const std::vector<Node>& exp, uint32_t index = 0);

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
