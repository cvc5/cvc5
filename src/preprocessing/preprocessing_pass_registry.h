/*********************                                                        */
/*! \file preprocessing_pass_registry.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andres Noetzli, Justin Xu, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief The preprocessing pass registry
 **
 ** This file defines the classes PreprocessingPassRegistry, which keeps track
 ** of the available preprocessing passes.
 **/
#include "cvc4_private.h"

#ifndef CVC4__PREPROCESSING__PREPROCESSING_PASS_REGISTRY_H
#define CVC4__PREPROCESSING__PREPROCESSING_PASS_REGISTRY_H

#include <memory>
#include <string>
#include <unordered_map>

#include "preprocessing/preprocessing_pass.h"

namespace CVC4 {
namespace preprocessing {

class PreprocessingPassContext;

/**
 * The PreprocessingPassRegistry keeps track of the available preprocessing
 * passes and how to create instances of those passes. This class is intended
 * to be used as a singleton and can be shared between threads (assuming that
 * the memory allocator is thread-safe) as well as different solver instances.
 */
class PreprocessingPassRegistry {
 public:
  /**
   * Gets the single instance of this class.
   */
  static PreprocessingPassRegistry& getInstance();

  /**
   * Registers a pass. Do not call this directly, use the `RegisterPass` class
   * instead.
   *
   * @param name The name of the preprocessing pass to register
   * @param ctor A function that creates an instance of the pass given a
   *             preprocessing pass context
   */
  void registerPassInfo(
      const std::string& name,
      std::function<PreprocessingPass*(PreprocessingPassContext*)> ctor);

  /**
   * Creates an instance of a pass.
   *
   * @param ppCtx The preprocessing pass context to pass to the preprocessing
   *              pass constructor
   * @param name The name of the pass to create an instance of
   */
  PreprocessingPass* createPass(PreprocessingPassContext* ppCtx,
                                const std::string& name);

  /**
   * Returns a sorted list of available preprocessing passes.
   */
  std::vector<std::string> getAvailablePasses();

  /**
   * Checks whether a pass with a given name is available.
   *
   * @param name The name of the pass to check for
   */
  bool hasPass(const std::string& name);

 private:
  /**
   * Private constructor for the preprocessing pass registry. The
   * registry is a singleton and no other instance should be created.
   */
  PreprocessingPassRegistry();

  /**
   * Map of available preprocessing passes, mapping from preprocessing pass
   * name to a function that constructs a corresponding instance.
   */
  std::unordered_map<
      std::string,
      std::function<PreprocessingPass*(PreprocessingPassContext*)> >
      d_ppInfo;
};  // class PreprocessingPassRegistry

}  // namespace preprocessing
}  // namespace CVC4

#endif /* CVC4__PREPROCESSING__PREPROCESSING_PASS_REGISTRY_H */
