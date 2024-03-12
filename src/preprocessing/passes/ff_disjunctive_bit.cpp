/******************************************************************************
 * Top contributors (to current version):
 *   Alex Ozdemir
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * replace disjunctive bit constraints with polynomial bit constraints
 *
 * example: x = 0 OR x = 1 becomes x * x = x
 */

#include "preprocessing/passes/ff_disjunctive_bit.h"

// external includes

// std includes

// internal includes
#include "preprocessing/assertion_pipeline.h"
#include "theory/ff/parse.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

FfDisjunctiveBit::FfDisjunctiveBit(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ff-disjunctive-bit")
{
}

PreprocessingPassResult FfDisjunctiveBit::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  auto nm = nodeManager();
  for (uint64_t i = 0, n = assertionsToPreprocess->size(); i < n; ++i)
  {
    Node fact = (*assertionsToPreprocess)[i];
    std::optional<Node> var = theory::ff::parse::disjunctiveBitConstraint(fact);
    if (var.has_value())
    {
      Trace("ff::disjunctive-bit") << "rw bit constr: " << *var << std::endl;
      Node var2 = nm->mkNode(Kind::FINITE_FIELD_MULT, *var, *var);
      assertionsToPreprocess->replace(i, var2.eqNode(*var));
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
