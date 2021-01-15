/*********************                                                        */
/*! \file strings_eager_pp.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The strings eager preprocess utility
 **/

#include "preprocessing/passes/strings_eager_pp.h"


namespace CVC4 {
namespace preprocessing {
namespace passes {

using namespace CVC4::theory;


StringsEagerPp::StringsEagerPp(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "strings-eager-pp"){};


PreprocessingPassResult StringsEagerPp::applyInternal(
  AssertionPipeline* assertionsToPreprocess)
{	
  for (size_t i = 0, nasserts = assertionsToPreprocess->size(); i < nasserts; ++i) {
    
  }

  return PreprocessingPassResult::NO_CONFLICT;
}


}  // namespace passes
}  // namespace preprocessing
}  // namespace CVC4
