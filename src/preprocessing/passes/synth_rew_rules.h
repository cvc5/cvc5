/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A technique for synthesizing candidate rewrites of the form t1 = t2,
 * where t1 and t2 are subterms of the input.
 */

#ifndef CVC5__PREPROCESSING__PASSES__SYNTH_REW_RULES_H
#define CVC5__PREPROCESSING__PASSES__SYNTH_REW_RULES_H

#include "preprocessing/preprocessing_pass.h"

namespace cvc5::internal {
namespace preprocessing {
namespace passes {

/**
 * This class rewrites the input assertions into a sygus conjecture over a
 * grammar whose terms are "abstractions" of the subterms of
 * assertionsToPreprocess. In detail, assume our input was
 *    bvadd( bvlshr( bvadd( a, 4 ), 1 ), b ) = 1
 * This class constructs this grammar:
 *    A -> T1 | T2 | T3 | T4 | Tv
 *    T1 -> bvadd( T2, Tv ) | x | y
 *    T2 -> bvlshr( T3, T4 ) | x | y
 *    T3 -> bvadd( Tv, T5 ) | x | y
 *    T4 -> 1 | x | y
 *    T5 -> 4 | x | y
 *    Tv -> x | y
 * Notice that this grammar generates all subterms of the input where leaves
 * are replaced by the variables x and/or y. The number of variable constructors
 * (x and y in this example) used in this construction is configurable via
 * sygus-rr-synth-input-nvars. The default for this value is 3, the
 * justification is that this covers most of the interesting rewrites while
 * not being too inefficient.
 *
 * Also notice that currently, this grammar construction admits terms that
 * do not necessarily match any in the input. For example, the above grammar
 * admits bvlshr( x, x ), which is not matchable with a subterm of the input.
 *
 * Notice that Booleans are treated specially unless the option
 * --sygus-rr-synth-input-bool is enabled, since we do not by default want to
 * generate purely propositional rewrites. In particular, we allocate only
 * one Boolean variable (to ensure that no sygus type is non-empty).
 *
 * It then rewrites the input into the negated sygus conjecture
 *   forall x : ( BV_n x BV_n ) -> BV_n. false
 * where x has the sygus grammar restriction A from above. This conjecture can
 * then be processed using --sygus-rr-synth in the standard way, which will
 * cause candidate rewrites to be printed on the output stream. If multiple
 * types are present, then we generate a conjunction of multiple synthesis
 * conjectures, which we enumerate terms for in parallel.
 */
class SynthRewRulesPass : public PreprocessingPass
{
 public:
  SynthRewRulesPass(PreprocessingPassContext* preprocContext);

  static std::vector<TypeNode> getGrammarsFrom(
      const std::vector<Node>& assertions, uint64_t nvars);

 protected:
  static std::map<TypeNode, TypeNode> constructTopLevelGrammar(
      const std::vector<Node>& assertions, uint64_t nvars);
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5::internal

#endif /* CVC5__PREPROCESSING__PASSES__SYNTH_REW_RULES_H */
