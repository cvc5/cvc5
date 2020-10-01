/*********************                                                        */
/*! \file bv_eager_atoms.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Wrap assertions in BITVECTOR_EAGER_ATOM nodes.
 **
 ** This preprocessing pass wraps all assertions in BITVECTOR_EAGER_ATOM nodes
 ** and allows to use eager bit-blasting in the BV solver.
 **/


#include "preprocessing/passes/bv_eager_atoms.h"

#include "theory/theory_model.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

BvEagerAtoms::BvEagerAtoms(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "bv-eager-atoms"){};

PreprocessingPassResult BvEagerAtoms::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  theory::TheoryModel* tm = d_preprocContext->getTheoryEngine()->getModel();
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, size = assertionsToPreprocess->size(); i < size; ++i)
  {
    TNode atom = (*assertionsToPreprocess)[i];
    Node eager_atom = nm->mkNode(kind::BITVECTOR_EAGER_ATOM, atom);
    tm->addSubstitution(eager_atom, atom);
    assertionsToPreprocess->replace(i, eager_atom);
  }
  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
