/*********************                                                        */
/*! \file apply_substs.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Aina Niemetz, Andres Noetzli, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Apply substitutions preprocessing pass.
 **
 ** Apply top level substitutions to assertions, rewrite, and store back into
 ** assertions.
 **/

#include "preprocessing/passes/apply_substs.h"

#include "context/cdo.h"
#include "theory/rewriter.h"
#include "theory/substitutions.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

ApplySubsts::ApplySubsts(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "apply-substs")
{
}

PreprocessingPassResult ApplySubsts::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  if (!options::unsatCores())
  {
    Chat() << "applying substitutions..." << std::endl;
    Trace("apply-substs") << "SmtEnginePrivate::processAssertions(): "
                      << "applying substitutions" << std::endl;
    // TODO(#1255): Substitutions in incremental mode should be managed with a
    // proper data structure.

    theory::SubstitutionMap& substMap =
        d_preprocContext->getTopLevelSubstitutions();
    unsigned size = assertionsToPreprocess->size();
    for (unsigned i = 0; i < size; ++i)
    {
      if (assertionsToPreprocess->isSubstsIndex(i))
      {
        continue;
      }
      Trace("apply-substs") << "applying to " << (*assertionsToPreprocess)[i]
                        << std::endl;
      d_preprocContext->spendResource(
          ResourceManager::Resource::PreprocessStep);
      assertionsToPreprocess->replace(i,
                                      theory::Rewriter::rewrite(substMap.apply(
                                          (*assertionsToPreprocess)[i])));
      Trace("apply-substs") << "  got " << (*assertionsToPreprocess)[i]
                        << std::endl;
    }
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
