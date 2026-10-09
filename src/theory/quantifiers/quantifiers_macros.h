/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Utility for detecting quantifier macro definitions.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_MACROS_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_MACROS_H

#include <map>
#include <vector>

#include "context/cdhashmap.h"
#include "expr/node.h"
#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
class Options;
namespace theory {
namespace quantifiers {

/**
 * A utility for inferring macros from quantified formulas. This can be seen as
 * a method for putting quantified formulas in solved form, e.g.
 *   forall x. P(x) ---> P = (lambda x. true)
 */
class QuantifiersMacros : protected EnvObj, public ProofGenerator
{
 public:
  QuantifiersMacros(Env& env);
  ~QuantifiersMacros() {}
  /**
   * Called on quantified formulas lit of the form
   *   forall x1 ... xn. n = ndef
   * where n is of the form U(x1...xn). Returns an equality of the form
   *   U = lambda x1 ... xn. ndef
   * if this is a legal macro definition for U, and the null node otherwise.
   * The formula and U must have no free bound variables.
   *
   * @param lit The body of the quantified formula
   * @param reqGround Whether we require the macro definition to be ground,
   * i.e. does not contain quantified formulas as subterms.
   * @return If a macro can be inferred, an equality of the form
   * (op = lambda x1 ... xn. def)), or the null node otherwise.
   */
  Node solve(Node lit, bool reqGround = false);
  /**
   * Version of the above that does not depend on the environment.
   */
  static Node getMacroDefinition(const Options& opts,
                                 Node lit,
                                 bool reqGround = false);
  /**
   * Remember that eq was inferred from tn in ppAssert, enabling this class to
   * provide a proof of eq on demand.
   */
  void notifySolved(const Node& eq, TrustNode tn);
  /** ProofGenerator interface */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;

 private:
  /**
   * Return true n is an APPLY_UF with pairwise unique BOUND_VARIABLE as
   * children.
   */
  static bool isBoundVarApplyUf(Node n);
  /**
   * Returns true if n contains op, or if n contains a quantified formula
   * as a subterm and reqGround is true.
   */
  static bool containsBadOp(Node n, Node op, bool reqGround);
  /**
   * Return true if n preserves trigger variables in quantified formula q, that
   * is, triggers can be inferred containing all variables in q in term n.
   */
  static bool preservesTriggerVariables(const Options& opts, Node q, Node n);
  /**
   * From n, get a list of possible subterms of n that could be the head of a
   * macro definition.
   */
  static void getMacroCandidates(Node n,
                                 std::vector<Node>& candidates,
                                 std::map<Node, bool>& visited);
  /**
   * Solve n in literal lit, return n' such that n = n' is equivalent to lit
   * if possible, or null otherwise.
   */
  static Node solveInEquality(Node n, Node lit);
  /**
   * Called when we have inferred a quantified formula is of the form
   *   forall x1 ... xn. n = ndef
   * where n is of the form U(x1...xn).
   */
  static Node solveEq(Node n, Node ndef);
  /**
   * Returns the macro fdef, which originated from lit. This method is for
   * debugging.
   */
  static Node returnMacro(Node fdef, Node lit);
  /**
   * Mapping from inferred macro equalities to the quantified formulas they
   * originated from.
   */
  context::CDHashMap<Node, TrustNode> d_ppsolves;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /*CVC5__THEORY__QUANTIFIERS__QUANTIFIER_MACROS_H */
