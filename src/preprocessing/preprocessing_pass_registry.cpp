/*********************                                                        */
/*! \file preprocessing_pass_registry.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Justin Xu, Yoni Zohar
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass registry
 **
 ** This file defines the classes PreprocessingPassRegistry, which keeps track
 ** of the available preprocessing passes, and RegisterPass, which registers a
 ** preprocessing pass with the registry.
 **/

#include "preprocessing/preprocessing_pass_registry.h"

#include <algorithm>
#include <utility>

#include "base/cvc4_assert.h"
#include "base/output.h"
#include "preprocessing/preprocessing_pass.h"

namespace CVC4 {
namespace preprocessing {

PreprocessingPassRegistry& PreprocessingPassRegistry::getInstance()
{
  static PreprocessingPassRegistry* ppReg = new PreprocessingPassRegistry();
  return *ppReg;
}

void PreprocessingPassRegistry::registerPassInfo(
    const std::string& name,
    std::function<PreprocessingPass*(PreprocessingPassContext*)> ctor)
{
  d_ppInfo[name] = ctor;
}

PreprocessingPass* PreprocessingPassRegistry::createPass(
    PreprocessingPassContext* ppCtx, const std::string& name)
{
  return d_ppInfo[name](ppCtx);
}

std::vector<std::string> PreprocessingPassRegistry::getAvailablePasses()
{
  std::vector<std::string> passes;
  for (const auto& info : d_ppInfo)
  {
    passes.push_back(info.first);
  }
  std::sort(passes.begin(), passes.end());
  return passes;
}

bool PreprocessingPassRegistry::hasPass(const std::string& name)
{
  return d_ppInfo.find(name) != d_ppInfo.end();
}

}  // namespace preprocessing
}  // namespace CVC4
