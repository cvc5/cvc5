
/******************************************************************************
 * Top contributors (to current version):
 *  Luís Felipe Ramos Ferreira, Haniel Barbosa
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Applies the preprocessing of a LIA formula into a automata problem and
 * calls a external automata solver. Algebraic Reasoning Meets Automata in
Solving Linear Integer Arithmetic
 *
 *
 * Calls Theory::preprocess(...) on every assertion of the formula.
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__AUTOMATA_H
#define CVC5__PREPROCESSING__PASSES__AUTOMATA_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

class Automata : public PreprocessingPass
{
 public:
  Automata(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  // the DFA itself. Initially it will be done for a single formula, for
  // example, x + 2y <= 1, so we have a adjacency list of the RHS values of hte
  // inequality.
  std::map<int, std::map<int, std::pair<int, int>>> dfa;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__AUTOMATA_H */
