/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A proof generator for lemmas that use ProofRule::ARITH_MULT_ABS_COMPARISON.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXT__ARITH_NL_COMPARE_PROOF_GEN_H
#define CVC5__THEORY__ARITH__NL__EXT__ARITH_NL_COMPARE_PROOF_GEN_H

#include "proof/proof_generator.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

/**
 * A proof generator that takes lemmas InferenceId::ARITH_NL_COMPARISON and
 * gives them a proof in terms of ProofRule::ARITH_MULT_ABS_COMPARISON.
 *
 * This involves several things:
 * (1) It makes the proof involve literals of the form (abs x) ~ (abs y)
 * instead of their rewritten form (MonomialCheck::mkLit).
 * (2) Reorders the explanation to match the conclusion.
 * (3) Groups the disequalities with the proper explanation.
 * (4) Uses repetition of the explanation to match exponents > 1.
 *
 * For example, after santizing the literals in (1), the lemma:
 * (=> (and (= (abs x) (abs z)) (> (abs w) (abs y)) (> (abs w) (abs 1)) (not (=
 * x 0)))
 *     (> (abs (* x x w w)) (abs (* z z y))))
 * is based on the proof step:
 * (=> (and
 *        (and (= (abs x) (abs z)) (not (= x 0)))
 *        (and (= (abs x) (abs z)) (not (= x 0)))
 *        (> (abs w) (abs y))
 *        (> (abs w) (abs 1))
 *     )
 *     (> (abs (* x x w w)) (abs (* z z y 1)))
 * )
 *
 */
class ArithNlCompareProofGenerator : protected EnvObj, public ProofGenerator
{
 public:
  ArithNlCompareProofGenerator(Env& env);
  virtual ~ArithNlCompareProofGenerator();
  /**
   * Get the proof for fact, which is a lemma with id
   * InferenceId::ARITH_NL_COMPARISON.
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;
  /**
   * Make the product of terms in c.
   */
  static Node mkProduct(NodeManager* nm, const std::vector<Node>& c);
  /**
   * Make literal that compares the absolute value of a and b with kind k.
   */
  static Node mkLit(NodeManager* nm, Kind k, const Node& a, const Node& b);
  /**
   * Mark that the formula olit corresponds to the literal that compares the
   * absolute values of a and b with kind k.
   */
  static void setCompareLit(
      NodeManager* nm, Node olit, Kind k, const Node& a, const Node& b);
  /**
   * Get the literal that was marked by the above method for olit, if the
   * null node is not applicable.
   */
  static Node getCompareLit(const Node& olit);
  /**
   * Given a literal lit constructed by mkLit above, this decomposes lit
   * into the arguments passed to mkLit above and adds the left hand side
   * to a and right hand side to b.
   */
  static Kind decomposeCompareLit(const Node& lit,
                                  std::vector<Node>& a,
                                  std::vector<Node>& b);
  /**
   * Adds the product terms of n to vec.
   */
  static void addProduct(const Node& n, std::vector<Node>& vec);
  /**
   * Is lit a disequality with zero? If lit is of the form (not (= t 0)), this
   * method returns t, otherwise it returns the null node.
   */
  static Node isDisequalZero(const Node& lit);
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__NL_MONOMIAL_H */
