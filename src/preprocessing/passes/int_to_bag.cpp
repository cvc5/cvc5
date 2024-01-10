/******************************************************************************
 * Top contributors (to current version):
 *   Yoni Zohar, Gereon Kremer, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The BVToInt preprocessing pass.
 *
 * Converts bit-vector operations into integer operations.
 *
 */

#include "preprocessing/passes/int_to_bag.h"

#include <cmath>
#include <string>
#include <unordered_map>
#include <vector>

#include "expr/node.h"
#include "expr/node_traversal.h"
#include "options/smt_options.h"
#include "options/uf_options.h"
#include "theory/bv/theory_bv_rewrite_rules_operator_elimination.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/bv/theory_bv_rewrite_rules_simplification.h"
#include "theory/rewriter.h"

namespace cvc5::internal {
    namespace preprocessing {
        namespace passes {

            using namespace std;
            using namespace cvc5::internal::theory;

            IntToBag::IntToBag(PreprocessingPassContext *preprocContext)
                    : PreprocessingPass(preprocContext, "int-to-bag") {}

            PreprocessingPassResult IntToBag::applyInternal(
                    AssertionPipeline *assertionsToPreprocess) {
                return PreprocessingPassResult::NO_CONFLICT;
            }

        }  // namespace passes
    }  // namespace preprocessing
}  // namespace cvc5::internal