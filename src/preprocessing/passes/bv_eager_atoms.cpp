/******************************************************************************
 * Top contributors (to current version):
 *   Mathias Preiner, Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrap assertions in BITVECTOR_EAGER_ATOM nodes.
 *
 * This preprocessing pass wraps all assertions in BITVECTOR_EAGER_ATOM nodes
 * and allows to use eager bit-blasting in the BV solver.
 */

#include "preprocessing/passes/bv_eager_atoms.h"

#include "preprocessing/assertion_pipeline.h"
#include "preprocessing/preprocessing_pass_context.h"
#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

BvEagerAtoms::BvEagerAtoms(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-eager-atoms"){};

PreprocessingPassResult BvEagerAtoms::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    TNode atom = (*assertionsToPreprocess)[i];
    if (atom.isConst())
    {
      // don't bother making true/false into atoms
      continue;
    }
    Node eager_atom = nm->mkNode(kind::BITVECTOR_EAGER_ATOM, atom);
    assertionsToPreprocess->replace(i, eager_atom);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal
