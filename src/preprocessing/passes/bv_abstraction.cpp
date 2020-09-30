/*********************                                                        */
/*! \file bv_abstraction.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The BvAbstraction preprocessing pass
 **
 ** Abstract common structures over small domains to UF. This preprocessing
 ** is particularly useful on QF_BV/mcm benchmarks and can be enabled via
 ** option `--bv-abstraction`.
 ** For more information see 3.4 Refactoring Isomorphic Circuits in [1].
 **
 ** [1] Liana Hadarean, An Efficient and Trustworthy Theory Solver for
 **     Bit-vectors in Satisfiability Modulo Theories
 **     https://cs.nyu.edu/media/publications/hadarean_liana.pdf
 **/

#include "preprocessing/passes/bv_abstraction.h"

#include <vector>

#include "options/bv_options.h"
#include "theory/bv/theory_bv.h"
#include "theory/rewriter.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

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
  bool changed = bv_theory->applyAbstraction(assertions, new_assertions);
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    assertionsToPreprocess->replace(i, Rewriter::rewrite(new_assertions[i]));
  }
  // If we are using the lazy solver and the abstraction applies, then UF
  // symbols were introduced.
  if (options::bitblastMode() == options::BitblastMode::LAZY && changed)
  {
    d_preprocContext->widenLogic(theory::THEORY_UF);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
