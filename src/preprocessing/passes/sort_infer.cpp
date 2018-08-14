/*********************                                                        */
/*! \file sort_infer.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Symmetry breaker module
 **/

#include "preprocessing/passes/sort_infer.h"

#include "options/uf_options.h"
#include "options/smt_options.h"

using namespace std;

namespace CVC4 {
namespace preprocessing {
namespace passes {


SortInferencePass::SortInferencePass(PreprocessingPassContext* preprocContext, SortInference * si)
    : PreprocessingPass(preprocContext, "sort-inference"), d_si(si){}

PreprocessingPassResult SortInferencePass::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  if( options::sortInference() )
  {
    d_si->initialize( assertionsToPreprocess->ref() );
    std::map< Node, std::map< TypeNode, Node > > visited;
    for (unsigned i = 0, size = assertionsToPreprocess->size(); i<size; i++)
    {
      Node prev = (*assertionsToPreprocess)[i];
      Node next = d_si->simplify(prev, visited);
      if (next != prev)
      {
        assertionsToPreprocess->replace(i, next);
        Trace("sort_infer-preprocess") << "*** Preprocess SortInferencePass " << prev << endl;
        Trace("sort_infer-preprocess") << "   ...got " << (*assertionsToPreprocess)[i]
                                << endl;
      }
    }
    std::vector< Node > newAsserts;
    d_si->getNewAssertions(newAsserts);
    for( const Node& na : newAsserts )
    {
      Trace("sort_infer-preprocess") << "*** Preprocess SortInferencePass : new constraint " << na << endl;
      assertionsToPreprocess->push_back(na);
    }
  }
  // only need to compute monotonicity on the resulting formula if we are
  // using this option
  if( options::ufssFairnessMonotone() )
  {
    d_si->computeMonotonicity(assertionsToPreprocess->ref() );
  }
  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
