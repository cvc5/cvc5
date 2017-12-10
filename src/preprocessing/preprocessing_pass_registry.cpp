/*********************                                                        */
/*! \file preprocessing_pass_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass registry
 **
 ** The preprocessing pass registry.
 **/

#include "preprocessing/preprocessing_pass_registry.h"

#include <utility>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "preprocessing/preprocessing_pass.h"

namespace CVC4 {
namespace preprocessing {

void PreprocessingPassRegistry::registerPass(
    const std::string& ppName,
    std::unique_ptr<PreprocessingPass> preprocessingPass) {
  Debug("pp-registry") << "Registering pass " << ppName << std::endl;
  Assert(preprocessingPass != nullptr);
  Assert(!this->hasPass(ppName));
  d_stringToPreprocessingPass[ppName] = std::move(preprocessingPass);
}

bool PreprocessingPassRegistry::hasPass(const std::string& ppName) {
  return d_stringToPreprocessingPass.find(ppName) !=
         d_stringToPreprocessingPass.end();
}

PreprocessingPass* PreprocessingPassRegistry::getPass(
    const std::string& ppName) {
  Assert(this->hasPass(ppName));
  return d_stringToPreprocessingPass[ppName].get();
}

}  // namespace preprocessing
}  // namespace CVC4
