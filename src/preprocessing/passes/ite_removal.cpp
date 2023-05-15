/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Remove ITEs from the assertions.
 *
 * [[ Add lengthier description here ]]
 * \todo document this file
 */

#include "preprocessing/passes/ite_removal.h"

#include "options/smt_options.h"
#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "prop/prop_engine.h"
#include "theory/rewriter.h"
#include "theory/theory_preprocessor.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using namespace cvc5::internal::theory;

// TODO (project #42): note this preprocessing pass is deprecated
IteRemoval::IteRemoval(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ite-removal")
{
}

PreprocessingPassResult IteRemoval::applyInternal(AssertionPipeline* assertions)
{
  d_preprocContext->spendResource(Resource::PreprocessStep);

  IteSkolemMap& imap = assertions->getIteSkolemMap();
  // Remove all of the ITE occurrences and normalize
  prop::PropEngine* pe = d_preprocContext->getPropEngine();
  for (unsigned i = 0, size = assertions->size(); i < size; ++i)
  {
    Node assertion = (*assertions)[i];
    std::vector<SkolemLemma> newAsserts;
    TrustNode trn = pe->removeItes(assertion, newAsserts);
    if (!trn.isNull())
    {
      // process
      assertions->replaceTrusted(i, trn);
    }
    for (const SkolemLemma& lem : newAsserts)
    {
      imap[assertions->size()] = lem.d_skolem;
      assertions->pushBackTrusted(lem.d_lemma);
    }
  }
  for (unsigned i = 0, size = assertions->size(); i < size; ++i)
  {
    assertions->replace(i, rewrite((*assertions)[i]));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
