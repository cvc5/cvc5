/*********************                                                        */
/*! \file ite_removal.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Remove ITEs from the assertions
 **
 ** [[ Add lengthier description here ]]
 ** \todo document this file
 **/

#include "preprocessing/passes/ite_removal.h"

#include "theory/rewriter.h"
#include "theory/theory_preprocessor.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

// TODO (project #42): note this preprocessing pass is deprecated
IteRemoval::IteRemoval(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "ite-removal")
{
}

PreprocessingPassResult IteRemoval::applyInternal(AssertionPipeline* assertions)
{
  d_preprocContext->spendResource(ResourceManager::Resource::PreprocessStep);

  IteSkolemMap& imap = assertions->getIteSkolemMap();
  // Remove all of the ITE occurrences and normalize
  prop::PropEngine* pe = d_preprocContext->getPropEngine();
  for (unsigned i = 0, size = assertions->size(); i < size; ++i)
  {
    Node assertion = (*assertions)[i];
    std::vector<theory::TrustNode> newAsserts;
    std::vector<Node> newSkolems;
    TrustNode trn = pe->removeItes(assertion, newAsserts, newSkolems);
    if (!trn.isNull())
    {
      // process
      assertions->replaceTrusted(i, trn);
    }
    Assert(newSkolems.size() == newAsserts.size());
    for (unsigned j = 0, nnasserts = newAsserts.size(); j < nnasserts; j++)
    {
      imap[newSkolems[j]] = assertions->size();
      assertions->pushBackTrusted(newAsserts[j]);
      // new assertions have a dependence on the node (old pf architecture)
      if (options::unsatCores() && !options::proofNew())
      {
        ProofManager::currentPM()->addDependence(newAsserts[j].getProven(),
                                                 assertion);
      }
    }
  }
  for (unsigned i = 0, size = assertions->size(); i < size; ++i)
  {
    assertions->replace(i, Rewriter::rewrite((*assertions)[i]));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
