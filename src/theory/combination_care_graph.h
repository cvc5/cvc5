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
 * Management of a care graph based approach for theory combination.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__COMBINATION_CARE_GRAPH__H
#define CVC5__THEORY__COMBINATION_CARE_GRAPH__H

#include <vector>

#include "theory/combination_engine.h"

namespace cvc5::internal {

class TheoryEngine;

namespace theory {

/**
 * Manager for doing theory combination using care graphs. This is typically
 * done via a distributed equality engine architecture.
 */
class CombinationCareGraph : public CombinationEngine
{
 public:
  CombinationCareGraph(Env& env,
                       TheoryEngine& te,
                       const std::vector<Theory*>& paraTheories);
  ~CombinationCareGraph();

  bool buildModel() override;
  /**
   * Combine theories using a care graph.
   */
  void combineTheories() override;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__COMBINATION_DISTRIBUTED__H */
