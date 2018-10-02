/*********************                                                        */
/*! \file preprocessing_pass_registry.h
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
 ** The preprocessing pass registry keeps track of all the instances of
 ** preprocessing passes. Upon creation, preprocessing passes are registered in
 ** the registry, which then takes ownership of them.
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROCESSING__PREPROCESSING_PASS_REGISTRY_H
#define __CVC4__PREPROCESSING__PREPROCESSING_PASS_REGISTRY_H

#include <memory>
#include <string>
#include <unordered_map>

#include "preprocessing/preprocessing_pass.h"

namespace CVC4 {
namespace preprocessing {

class PreprocessingPassRegistry {
 public:
  /**
   *  Registers a pass with a unique name and takes ownership of it.
   */
  void registerPass(const std::string& ppName,
                    std::unique_ptr<PreprocessingPass> preprocessingPass);

  /**
   * Retrieves a pass with a given name from registry.
   */
  PreprocessingPass* getPass(const std::string& ppName);

  /**
   Clears all passes from the registry.
   */
  void unregisterPasses();

 private:
  bool hasPass(const std::string& ppName);

  /* Stores all the registered preprocessing passes. */
  std::unordered_map<std::string, std::unique_ptr<PreprocessingPass>>
      d_stringToPreprocessingPass;
};  // class PreprocessingPassRegistry

}  // namespace preprocessing
}  // namespace CVC4

#endif /* __CVC4__PREPROCESSING__PREPROCESSING_PASS_REGISTRY_H */
