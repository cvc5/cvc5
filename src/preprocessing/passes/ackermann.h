/******************************************************************************
 * Top contributors (to current version):
 *   Aina Niemetz, Ying Sheng, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Ackermannization preprocessing pass.
 *
 * This implements the Ackermannization preprocessing pass, which enables
 * very limited theory combination support for eager bit-blasting via
 * Ackermannization. It reduces constraints over the combination of the
 * theories of fixed-size bit-vectors and uninterpreted functions as
 * described in
 *   Liana Hadarean, An Efficient and Trustworthy Theory Solver for
 *   Bit-vectors in Satisfiability Modulo Theories.
 *   https://cs.nyu.edu/media/publications/hadarean_liana.pdf
 */

#include "cvc5_private.h"

#ifndef CVC5__PREPROCESSING__PASSES__ACKERMANN_H
#define CVC5__PREPROCESSING__PASSES__ACKERMANN_H

#include <unordered_map>

#include "expr/node.h"
#include "preprocessing/preprocessing_pass.h"
#include "theory/logic_info.h"
#include "theory/substitutions.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

using TNodeSet = std::unordered_set<TNode>;
using FunctionToArgsMap = std::unordered_map<TNode, TNodeSet>;
using USortToBVSizeMap = std::unordered_map<TypeNode, size_t>;

class Ackermann : public PreprocessingPass
{
 public:
  Ackermann(PreprocessingPassContext* preprocContext);

 protected:
  /**
   * Apply Ackermannization as follows:
   *
   * - For each application f(X) where X = (x1, . . . , xn), introduce a fresh
   *   variable f_X and use it to replace all occurrences of f(X).
   *
   * - For each f(X) and f(Y) with X = (x1, . . . , xn) and Y = (y1, . . . , yn)
   *   occurring in the input formula, add the following lemma:
   *     (x_1 = y_1 /\ ... /\ x_n = y_n) => f_X = f_Y
   *
   * - For each uninterpreted sort S, suppose k is the number of variables with
   *   sort S, then for each such variable X, introduce a fresh variable BV_X
   *   with BV with size log_2(k)+1 and use it to replace all occurrences of X.
   */
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;

 private:
  /* Map each function to a set of terms associated with it */
  FunctionToArgsMap d_funcToArgs;
  /* Map each function-application term to the new Skolem variable created by
   * ackermannization */
  theory::SubstitutionMap d_funcToSkolem;
  /* Map each variable with uninterpreted sort to the new Skolem BV variable
   * created by ackermannization */
  theory::SubstitutionMap d_usVarsToBVVars;
  /* Map each uninterpreted sort to the number of variables in this sort. */
  USortToBVSizeMap d_usortCardinality;
  LogicInfo d_logic;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__ACKERMANN_H */
