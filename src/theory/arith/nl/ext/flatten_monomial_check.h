/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Tim King
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Check for monomial bound inference lemmas.
 */

#ifndef CVC5__THEORY__ARITH__NL__EXT__FLATTEN_MONOMIAL_CHECK_H
#define CVC5__THEORY__ARITH__NL__EXT__FLATTEN_MONOMIAL_CHECK_H

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/arith/inference_manager.h"
#include "theory/theory_state.h"

namespace cvc5::internal {
namespace theory {
namespace arith {
namespace nl {

class FlattenMonomialCheck : protected EnvObj
{
 public:
  FlattenMonomialCheck(Env& env, TheoryState& astate, InferenceManager& im);

  /**
   * Check flattening of monomials
   */
  void check(const std::vector<Node>& mvec);

 private:
  /** A reference to the arithmetic state object */
  TheoryState& d_astate;
  /** The inference manager that we push conflicts and lemmas to. */
  InferenceManager& d_im;
  /** 
   * Add to the flattened map. May add a lemma if ns already exists.
   */
  void addToFlattenMonMap(const Node& ns,
                          const Node& n,
                          std::map<Node, Node>& ffMap,
                          const std::map<Node, Node>& repEq);
};

}  // namespace nl
}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal

#endif
