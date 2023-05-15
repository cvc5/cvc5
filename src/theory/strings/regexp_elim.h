/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Techniques for eliminating regular expressions.
 */

#include "cvc5_private.h"
#ifndef CVC5__THEORY__STRINGS__REGEXP_ELIM_H
#define CVC5__THEORY__STRINGS__REGEXP_ELIM_H

#include "expr/node.h"
#include "proof/eager_proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace strings {

/** Regular expression membership elimination
 *
 * This class implements techniques for reducing regular expression memberships
 * to bounded integer quantifiers + extended function constraints.
 *
 * It is used by TheoryStrings during ppRewrite.
 */
class RegExpElimination : protected EnvObj
{
 public:
  /**
   * @param isAgg Whether aggressive eliminations are enabled
   * @param pnm The proof node manager to use (for proofs)
   * @param c The context to use (for proofs)
   */
  RegExpElimination(Env& env,
                    bool isAgg = false,
                    context::Context* c = nullptr);
  /** eliminate membership
   *
   * This method takes as input a regular expression membership atom of the
   * form (str.in.re x R). If this method returns a non-null node ret, then ret
   * is equivalent to atom.
   *
   * @param atom The node to eliminate
   * @param isAgg Whether we apply aggressive elimination techniques
   * @return The node with regular expressions eliminated, or null if atom
   * was unchanged.
   */
  static Node eliminate(Node atom, bool isAgg);

  /**
   * Return the trust node corresponding to rewriting n based on eliminate
   * above.
   */
  TrustNode eliminateTrusted(Node atom);

 private:
  /** return elimination
   *
   * This method is called when atom is rewritten to atomElim, and returns
   * atomElim. id is an identifier indicating the reason for the elimination.
   */
  static Node returnElim(Node atom, Node atomElim, const char* id);
  /** elimination for regular expression concatenation */
  static Node eliminateConcat(Node atom, bool isAgg);
  /** elimination for regular expression star */
  static Node eliminateStar(Node atom, bool isAgg);
  /** Are proofs enabled? */
  bool isProofEnabled() const;
  /** Are aggressive eliminations enabled? */
  bool d_isAggressive;
  /** An eager proof generator for storing proofs in eliminate trusted above */
  std::unique_ptr<EagerProofGenerator> d_epg;
}; /* class RegExpElimination */

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__STRINGS__REGEXP_ELIM_H */
