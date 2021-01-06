/*********************                                                        */
/*! \file str_len_simplify.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The str_len_simplify preprocessing pass
 **
 ** Simplifies Arithmetic nodes by calling
 ** CVC4::theory::strings::ArithEntail::check
 ** on each GEQ node.
 **/

#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PASSES__STR_LEN_SIMPLIFY_H
#define CVC4__PREPROCESSING__PASSES__STR_LEN_SIMPLIFY_H

#include "context/cdhashmap.h"
#include "context/cdo.h"
#include "context/context.h"
#include "preprocessing/preprocessing_pass.h"
#include "preprocessing/preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {
namespace passes {

using CDNodeMap = context::CDHashMap<Node, Node, NodeHashFunction>;

class StrLenSimplify : public PreprocessingPass
{
 public:
  StrLenSimplify(PreprocessingPassContext* preprocContext);

 protected:
  PreprocessingPassResult applyInternal(
      AssertionPipeline* assertionsToPreprocess) override;
  // the main function that simplifies n
  Node simplify(Node n);
  // A cache to store the simplified nodes
  CDNodeMap d_cache;
};

}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PASSES__STR_LEN_SIMPLIFY_H */
