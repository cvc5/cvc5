/*********************                                                        */
/*! \file synth_rew_rules.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief A technique for synthesizing candidate rewrites of the form t1 = t2,
 ** where t1 and t2 are subterms of the input.
 **/

#ifndef __CVC4__PREPROCESSING__PASSES__SYNTH_REW_RULES_H
#define __CVC4__PREPROCESSING__PASSES__SYNTH_REW_RULES_H

#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

/**
 * This class rewrites the input assertions into a sygus conjecture over a
 * grammar whose terms are "abstractions" of the subterms of
 * assertionsToPreprocess. In detail, assume our input was
 *    bvadd( bvshlr( bvadd( a, 4 ), 1 ), b ) = 1
 * This class constructs this grammar:
 *    A -> T1 | T2 | T3 | T4 | Tv
 *    T1 -> bvadd( T2, Tv ) | x | y
 *    T2 -> bvshlr( T3, T4 ) | x | y
 *    T3 -> bvadd( Tv, T5 ) | x | y
 *    T4 -> 1 | x | y
 *    T5 -> 4 | x | y
 *    Tv -> x | y
 * Notice that this grammar generates all subterms of the input where leaves
 * are replaced by the variables x and/or y (the number of variables allocated
 * by this class is configurable via sygus-rr-synth-input-nvars).
 *
 * It then rewrites the input into the negated sygus conjecture
 *   forall x : ( BV_n x BV_n ) -> BV_n. false
 * where x has the sygus grammar restriction A from above. This conjecture can
 * then be processed using --sygus-rr-synth in the standard way, which will
 * cause candidate rewrites to be printed on the output stream.
 */
class SynthRewRulesPass : public PreprocessingPass
{
 public:
  SynthRewRulesPass(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PASSES__SYNTH_REW_RULES_H */
