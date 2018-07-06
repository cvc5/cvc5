/*********************                                                        */
/*! \file preprocessing_pass_context.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Justin Xu, Mathias Preiner, Aina Niemetz
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass context for passes
 **
 ** The preprocessing pass context for passes.
 **/

#include "preprocessing_pass_context.h"

namespace CVC4 {
namespace preprocessing {

PreprocessingPassContext::PreprocessingPassContext(
    SmtEngine* smt, ResourceManager* resourceManager)
    : d_smt(smt), d_resourceManager(resourceManager)
{
}

void PreprocessingPassContext::widenLogic(theory::TheoryId id)
{
  LogicRequest req(*d_smt);
  req.widenLogic(id);
}

}  // namespace preprocessing
}  // namespace CVC4
