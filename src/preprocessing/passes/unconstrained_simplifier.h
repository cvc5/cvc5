/******************************************************************************
 * Top contributors (to current version):
 *   Clark Barrett, Andres Noetzli, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simplifications based on unconstrained variables
 *
 * This module implements a preprocessing phase which replaces certain
 * "unconstrained" expressions by variables.  Based on Roberto
 * Bruttomesso's PhD thesis.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING_PASSES_UNCONSTRAINED_SIMPLIFIER_H
#define CVC5__PREPROCESSING_PASSES_UNCONSTRAINED_SIMPLIFIER_H

#include <unordered_map>
#include <unordered_set>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "theory/substitutions.h"
#include "util/statistics_stats.h"

namespace cvc5::context {
class Context;
}
namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class UnconstrainedSimplifier : public PreprocessingPass
{
 public:
  UnconstrainedSimplifier(PreprocessingPassContext* preprocContext);

  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** number of expressions eliminated due to unconstrained simplification */
  IntStat d_numUnconstrainedElim;

  using TNodeCountMap = std::unordered_map<TNode, unsigned>;
  using TNodeMap = std::unordered_map<TNode, TNode>;
  using TNodeSet = std::unordered_set<TNode>;

  TNodeCountMap d_visited;
  TNodeMap d_visitedOnce;
  TNodeSet d_unconstrained;

  context::Context* d_context;
  theory::SubstitutionMap d_substitutions;

  /**
   * Visit all subterms in assertion. This method throws a LogicException if
   * there is a subterm that is unhandled by this preprocessing pass (e.g. a
   * quantified formula).
   */
  void visitAll(TNode assertion);
  Node newUnconstrainedVar(TypeNode t, TNode var);
  void processUnconstrained();
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif
