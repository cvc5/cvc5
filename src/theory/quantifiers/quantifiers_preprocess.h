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
 * Preprocessor for the theory of quantifiers.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_PREPROCESS_H
#define CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_PREPROCESS_H

#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * Module for doing preprocessing that is pertinent to quantifiers. These
 * operations cannot be done in the rewriter since e.g. preskolemization
 * depends on knowing the polarity of the position in which quantifiers occur.
 */
class QuantifiersPreprocess : protected EnvObj
{
 public:
  QuantifiersPreprocess(Env& env);
  /** preprocess
   *
   * This returns the result of applying simple quantifiers-specific
   * pre-processing to n, including but not limited to:
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
  using NodePolPairHashFunction = PairHashFunction<Node, bool, std::hash<Node>>;
  /**
   * Pre-skolemize quantifiers. Return the pre-skolemized form of n.
   *
   * @param n The formula to preskolemize.
   * @param polarity The polarity of n in the input.
   * @param fvs The free variables
   * @param visited Cache of visited (node, polarity) pairs.
   */
  Node preSkolemizeQuantifiers(
      Node n,
      bool polarity,
      std::vector<TNode>& fvs,
      std::unordered_map<std::pair<Node, bool>, Node, NodePolPairHashFunction>&
          visited) const;
  /**
   * Apply prenexing aggressively. Returns the prenex normal form of n.
   */
  Node computePrenexAgg(Node n, std::map<Node, Node>& visited) const;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__QUANTIFIERS_REWRITER_H */
