/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preprocessor for the theory of quantifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_PREPROCESSOR_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_PREPROCESSOR_H

#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {

class QuantifiersPreprocess : protected EnvObj
{
 public:
  QuantifiersPreprocess(Env& env);
  /** preprocess
   *
   * This returns the result of applying simple quantifiers-specific
   * preprocessing to n, including but not limited to:
   * - rewrite rule elimination,
   * - pre-skolemization,
   * - aggressive prenexing.
   * The argument isInst is set to true if n is an instance of a previously
   * registered quantified formula. If this flag is true, we do not apply
   * certain steps like pre-skolemization since we know they will have no
   * effect.
   *
   * The result is wrapped in a trust node of kind TrustNodeKind::REWRITE.
   */
  TrustNode preprocess(Node n, bool isInst = false) const;

 private:
  /** Pre-skolemize quantifiers */
  Node preSkolemizeQuantifiers(
      Node n,
      bool polarity,
      std::vector<TypeNode>& fvTypes,
      std::vector<TNode>& fvs,
      std::unordered_map<std::pair<Node, bool>, Node>& visited) const;
  /**
   * Apply prenexing aggressively. Returns the prenex normal form of n.
   */
  Node computePrenexAgg(Node n, std::map<Node, Node>& visited) const;
}; /* class QuantifiersRewriter */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */
