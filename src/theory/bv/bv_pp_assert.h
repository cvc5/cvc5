/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Method for handling cases of TheoryBv::ppAssert.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_PP_ASSERT_H
#define CVC5__THEORY__BV__BV_PP_ASSERT_H

#include "context/cdhashmap.h"
#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"
#include "theory/valuation.h"

namespace cvc5::internal {
namespace theory {

class TrustSubstitutionMap;

namespace bv {

/**
 * A class for implementing TheoryBv::ppAssert along with its proof tracking.
 */
class BvPpAssert : protected EnvObj, public ProofGenerator
{
 public:
  /** Constructor */
  BvPpAssert(Env& env, Valuation val);
  ~BvPpAssert();
  /**
   * Handles specific cases of ppAssert for theory of bit-vectors. Currently
   * this is limited to solving based on extract applied to variables e.g.:
   * (= (extract 3 1 x) #b00) becomes the substitution
   * x -> (concat (extract 7 4 x) #b00 (extract 0 0 x))
   *
   * @param tin The incoming literal with its proof.
   * @param outSubstitutions The substitutions to add to.
   * @return true if we added a substitution to outSubstitutions
   */
  bool ppAssert(TrustNode tin, TrustSubstitutionMap& outSubstitutions);
  /**
   * Get proof for fact, where fact is expected to be of the form (= x t) where
   * x -> t was a substitution added to outSubstitutions.
   *
   * Proofs are of the form:
   *
   * ... from input
   * ---------------------     -------------------------------- BV_PP_ASSERT
   * (= (extract n m x) y)     (= (extract n m x) y) (= x t_o))
   * ---------------------------------------------------------- EQ_RESOLVE
   * (= x t_o)
   * --------- MACRO_SR_PRED_TRANSFORM.
   * (= x t)
   *
   * where e.g. t_o is (concat (extract 7 4 x) #b00 (extract 0 0 x)) and
   * t is (concat purifyX74 #b00 purifyX00). The (trust) step BV_PP_ASSERT can
   * be justified by RARE rules bv-eq-extract-elim{1,2,3}
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;

 private:
  /** The valuation proxy. */
  Valuation d_valuation;
  /**
   * Mapping from solved equalities we gave to the substitution map and the
   * trust node they were derived from.
   */
  context::CDHashMap<Node, TrustNode> d_ppsolves;
  /**
   * Maps terms introduced by ppAssert to their original form that can be used
   * in justification, e.g.
   * (concat purifyX31 #b0) --> (concat (extract 3 1 x) #b0).
   */
  context::CDHashMap<Node, Node> d_origForm;
  /**
   * Add substitution x -> t which is justified based on the input equality
   * tin. This bookkeeps the connection to tin if proofs are enabled.
   */
  void addSubstitution(TrustSubstitutionMap& outSubstitutions,
                       const Node& x,
                       const Node& t,
                       TrustNode tin);
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__BV_PP_ASSERT_H */
