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
 * Management of a model-based approach for theory combination.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__COMBINATION_MODEL_BASED__H
#define CVC5__THEORY__COMBINATION_MODEL_BASED__H

#include <vector>

#include "theory/combination_engine.h"

namespace cvc5::internal {

class TheoryEngine;

namespace theory {

/**
 * This implements model-based theory combination. In this approach, we invoke
 * the standard model construction and afterwards check which terms have become
 * congruent. Note that since the model equality engine does *not* do
 * congruence, we compute this manually in the combineTheories method.
 * For each pair of congruent terms, we split on each pair of arguments that
 * are not already made equal in the theory that owns the congruent terms.
 *
 * For example, say f : Int -> Int and the initial model set
 * (f a) = 3, (f (+ b 1)) = 4. If we chose a = 2, b = 1, then
 * (1) a = (+ b 1) = 2
 * (2) (f 2) is set to both 3 and 4.
 * It should be the case that some argument of these two applications of f
 * are both shared terms, in this case a and b+1, in which case we add the
 * split a = b+1.
 *
 * Note that in the above case we had two applications of f that were congruent
 * *and* disequal. Note that terms that are congruent and equal also must be
 * treated similarly, as identifying them may violate theory constraints.
 * For example say c : Int -> D is a constructor of datatype D.
 * Say (c a) != (c (+ b 1)) is a constraint belonging to the theory of
 * datatypes, which is *not* communicated to the model. In this case, if the
 * model sets a = 2, b = 1, then (c a) = (c (+ b 1)) = (c 2),
 * i.e. they are congruent and equal, we split must split on a = b+1.
 *
 * It is important that this class check for splits for all cases of the above
 * form at once, as in practice there are many possible splits that should be
 * sent all at once, instead of considering one at a time.
 */
class CombinationModelBased : public CombinationEngine
{
 public:
  CombinationModelBased(Env& env,
                        TheoryEngine& te,
                        const std::vector<Theory*>& paraTheories);
  ~CombinationModelBased();
  /**
   * Reset model
   */
  void resetModel() override;
  /**
   * Build model
   */
  bool buildModel() override;
  /**
   * Combine theories using a care graph.
   */
  void combineTheories() override;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__COMBINATION_MODEL_BASED__H */
