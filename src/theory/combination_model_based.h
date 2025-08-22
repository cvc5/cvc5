/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Management of a care graph based approach for theory combination.
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
 */
class CombinationModelBased : public CombinationEngine
{
 public:
  CombinationModelBased(Env& env,
                        TheoryEngine& te,
                        const std::vector<Theory*>& paraTheories);
  ~CombinationModelBased();

  bool buildModel() override;
  /**
   * Combine theories using a care graph.
   */
  void combineTheories() override;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__COMBINATION_MODEL_BASED__H */
