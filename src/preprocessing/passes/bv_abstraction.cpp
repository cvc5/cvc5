/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BvAbstraction preprocessing pass.
 *
 * Abstract common structures over small domains to UF. This preprocessing
 * is particularly useful on QF_BV/mcm benchmarks and can be enabled via
 * option `--bv-abstraction`.
 * For more information see 3.4 Refactoring Isomorphic Circuits in [1].
 *
 * [1] Liana Hadarean, An Efficient and Trustworthy Theory Solver for
 *     Bit-vectors in Satisfiability Modulo Theories
 *     https://cs.nyu.edu/media/publications/hadarean_liana.pdf
 */

#include "preprocessing/passes/bv_abstraction.h"

#include <vector>

#include "options/bv_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/bv/theory_bv.h"
#include "theory/rewriter.h"
#include "theory/theory_engine.h"

namespace cvc5 {
namespace preprocessing {
namespace passes {

using namespace cvc5::theory;

BvAbstraction::BvAbstraction(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-abstraction"){};

PreprocessingPassResult BvAbstraction::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  std::vector<Node> new_assertions;
  std::vector<Node> assertions(assertionsToPreprocess->begin(),
                               assertionsToPreprocess->end());
  TheoryEngine* te = d_preprocContext->getTheoryEngine();
  bv::TheoryBV* bv_theory = static_cast<bv::TheoryBV*>(te->theoryOf(THEORY_BV));
  bv_theory->applyAbstraction(assertions, new_assertions);
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(i, Rewriter::rewrite(new_assertions[i]));
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
