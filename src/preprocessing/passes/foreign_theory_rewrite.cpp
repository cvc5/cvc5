/*********************                                                        */
/*! \file foreign_theory_rewrite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The foreign_theory_rewrite preprocessing pass
 **
 ** Simplifies nodes of one theory using rewrites from another.
 **/

#include "preprocessing/passes/foreign_theory_rewrite.h"

#include "expr/node_traversal.h"
#include "theory/strings/arith_entail.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;

ForeignTheoryRewrite::ForeignTheoryRewrite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "foreign-theory-rewrite"),
      d_cache(preprocContext->getUserContext()){};

Node ForeignTheoryRewrite::simplify(Node n) { assert(false); }

PreprocessingPassResult ForeignTheoryRewrite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  for (unsigned i = 0; i < assertionsToPreprocess->size(); ++i)
  {
    assertionsToPreprocess->replace(
        i, Rewriter::rewrite(simplify((*assertionsToPreprocess)[i])));
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
