/*********************                                                        */
/*! \file preprocessing_pass_registry.h
 ** \verbatim
 ** Top contributors (to current version):
 **  Justin Xu
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2017 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implementation for preprocessing pass registry
 **
 ** Implementation for preprocessing pass registry, which facilitates
 ** registering passes and deals with ownership of them to make sure that
 ** passes are properly disposed of. The registry is
 ** also responsible for making the API available to the passes. 
 **/
#include "cvc4_private.h"

#ifndef __CVC4__PREPROC__PREPROCESSING_PASS_REGISTRY_H
#define __CVC4__PREPROC__PREPROCESSING_PASS_REGISTRY_H

#include <memory>
#include <string>
#include <unordered_map>

#include "decision/decision_engine.h"
#include "preproc/preprocessing_pass_api.h"
#include "theory/arith/pseudoboolean_proc.h"
#include "theory/booleans/circuit_propagator.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace preproc {

class PreprocessingPass;

class PreprocessingPassRegistry {
 public:
  /* Initializes all the passes within PreprocessingPass map with API */
  void init(PreprocessingPassAPI* api);
  /* registers a pass with a unique name and takes ownership of it*/
  void registerPass(const std::string& ppName,
                    PreprocessingPass* preprocessingPass);
  /* method for retrieivng pass given name from registry */
  PreprocessingPass* getPass(const std::string& ppName);
  /* destructor that deletes all passes in map */
  ~PreprocessingPassRegistry();

 private:
  /* map that stores all the registered preprocessing passes */
  std::unordered_map<std::string, PreprocessingPass*>
      d_stringToPreprocessingPass;
};  // class PreprocessingPassRegistry

}  // namespace preproc
}  // namespace CVC4

#endif /* __CVC4__PREPROC__PREPROCESSING_PASS_REGISTRY_H */
