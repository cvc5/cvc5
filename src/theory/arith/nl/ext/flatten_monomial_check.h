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
 * Check for flattening monomials lemmas.
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

class FlattenMonProofGenerator;

/**
 * The flatten monomial check routine, which reasons about the associativity
 * of multiplication.
 * 
 * As a summary, this routine scans equivalence classes to build a substitution,
 * applies this substitution to non-linear multiplication terms and derives
 * equalities. For example, given equivalence classes:
 * 
 * { x, u*w, x*t }
 * { v, z*w }
 * { v*u }
 * { x*z }
 * { j, i }
 * 
 * We may infer the substitution { x -> u*w, v -> z*w, j -> i }. Applying this
 * substitution to v*u and rewriting gives z*w*u, similarly to x*z we
 * gives z*w*u. Hence we infer the lemma:
 *   x = u*w ^ v = z*w => v*u = x*z
 *
 * Note that equivalence classes with no variables are normalized such that all
 * variables in that class map to a representative variable. In the above
 * example, this would allow us to infer the lemma e.g. i=j => i*j*j = j*j*j.
 * Note that we ignore cyclic substitutions. For instance we could have inferred
 * x -> x*t in the example above, but do not since this is cyclic.
 * Furthermore note that 1 is treated as the empty monomial; all other constants
 * are ignored.
 */
class FlattenMonomialCheck : protected EnvObj
{
 public:
  FlattenMonomialCheck(Env& env, TheoryState& astate, InferenceManager& im);

  /**
   * Check flattening of monomials, as described above, which may add a pending
   * lemma to the inference manager.
   * @param mvec The list of variables appearing in monomials.
   */
  void check(const std::vector<Node>& mvec);

 private:
  /** A reference to the arithmetic state object */
  TheoryState& d_astate;
  /** The inference manager that we push conflicts and lemmas to. */
  InferenceManager& d_im;
  /** Proof generator */
  std::shared_ptr<FlattenMonProofGenerator> d_pfgen;
  /**
   * Add to the flattened map. May add a lemma if ns already exists in the
   * mapping ffMap.
   * @param ns The normalized form of a term.
   * @param n The original form of ns, prior to substitution + rewriting.
   * @param ffMap A map from normalized terms to their original forms.
   * @param repEq Mapping from representatives of the equality engine to the
   * term chosen for the substitution.
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
