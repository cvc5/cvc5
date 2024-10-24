
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

#include <bitset>

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__AUTOMATA_H
#define CVC5__PREPROCESSING__PASSES__AUTOMATA_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

struct AutomataEdge
{
  int endpoint;
  // assuming nr of coefficents at most 64
  int transition;
  bool acc;
};

class Automata : public PreprocessingPass
{
 public:
  Automata(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__AUTOMATA_H */
