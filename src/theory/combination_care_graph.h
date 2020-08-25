/*********************                                                        */
/*! \file combination_care_graph.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a care graph based approach for theory combination.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__COMBINATION_CARE_GRAPH__H
#define CVC4__THEORY__COMBINATION_CARE_GRAPH__H

#include <vector>

#include "theory/combination_engine.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * Manager for doing theory combination using care graphs. This is typically
 * done via a distributed equality engine architecture.
 */
class CombinationCareGraph : public CombinationEngine
{
 public:
  CombinationCareGraph(TheoryEngine& te,
                       const std::vector<Theory*>& paraTheories);
  ~CombinationCareGraph();

  bool buildModel() override;
  /**
   * Combine theories using a care graph.
   */
  void combineTheories() override;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_DISTRIBUTED__H */
