/*********************                                                        */
/*! \file unconstrained_simplifier.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Clark Barrett, Andres Noetzli, Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Simplifications based on unconstrained variables
 **
 ** This module implements a preprocessing phase which replaces certain
 ** "unconstrained" expressions by variables.  Based on Roberto
 ** Bruttomesso's PhD thesis.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING_PASSES_UNCONSTRAINED_SIMPLIFIER_H
#define CVC4__PREPROCESSING_PASSES_UNCONSTRAINED_SIMPLIFIER_H

#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "context/context.h"
#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"
#include "util/statistics_registry.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

class UnconstrainedSimplifier : public PreprocessingPass
{
 public:
  UnconstrainedSimplifier(PreprocessingPassContext* preprocContext);
  ~UnconstrainedSimplifier() override;

  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /** number of expressions eliminated due to unconstrained simplification */
  IntStat d_numUnconstrainedElim;

  using TNodeCountMap = std::unordered_map<TNode, unsigned, TNodeHashFunction>;
  using TNodeMap = std::unordered_map<TNode, TNode, TNodeHashFunction>;
  using TNodeSet = std::unordered_set<TNode, TNodeHashFunction>;

  TNodeCountMap d_visited;
  TNodeMap d_visitedOnce;
  TNodeSet d_unconstrained;

  context::Context* d_context;
  theory::SubstitutionMap d_substitutions;

  const LogicInfo& d_logicInfo;
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
}  // namespace CVC4

#endif
