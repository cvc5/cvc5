/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Abstract management of models for TheoryEngine.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__MODEL_MANAGER__H
#define CVC5__THEORY__MODEL_MANAGER__H

#include <memory>

#include "smt/env_obj.h"
#include "theory/ee_manager.h"
#include "theory/logic_info.h"

namespace cvc5::internal {

class TheoryEngine;
class Env;

namespace theory {

class TheoryEngineModelBuilder;
class TheoryModel;

/**
 * A base class for managing models. Its main feature is to implement a
 * buildModel command. Overall, its behavior is specific to the kind of equality
 * engine management mode we are using. In particular, the prepare model
 * method is a manager-specific way for setting up the equality engine of the
 * model in preparation for model building.
 */
class ModelManager : protected EnvObj
{
 public:
  ModelManager(Env& env, TheoryEngine& te, EqEngineManager& eem);
  virtual ~ModelManager();
  /**
   * Finish initializing this class, which allocates the model, the model
   * builder as well as the equality engine of the model. The equality engine
   * to use is determined by the virtual method initializeModelEqEngine.
   *
   * @param notify The object that wants to be notified for callbacks occurring
   */
  void finishInit(eq::EqualityEngineNotify* notify);
  /** Reset model, called during full effort check before the model is built */
  void resetModel();
  /**
   * Build the model. If we have yet to build the model on this round, this
   * method calls the (manager-specific) prepareModel method and then calls
   * finishBuildModel.
   *
   * @return true if model building was successful.
   */
  bool buildModel();
  /**
   * Have we called buildModel this round? Note this returns true whether or
   * not the model building was successful.
   */
  bool isModelBuilt() const;
  /**
   * Post process model, which is used as a way of each theory adding additional
   * information to the model after successfully building a model.
   */
  void postProcessModel(bool incomplete);
  /** Get a pointer to model object maintained by this class. */
  TheoryModel* getModel();
  //------------------------ finer grained control over model building
  /**
   * Prepare model, which is the manager-specific method for setting up the
   * equality engine of the model. This should assert all relevant information
   * about the model into the equality engine of d_model.
   *
   * @return true if we are in conflict (i.e. the equality engine of the model
   * equality engine is inconsistent).
   */
  virtual bool prepareModel() = 0;
  /**
   * Finish build model, which calls the theory model builder to assign values
   * to all equivalence classes. This should be run after prepareModel.
   *
   * @return true if model building was successful.
   */
  virtual bool finishBuildModel() const = 0;
  //------------------------ end finer grained control over model building
 protected:
  /**
   * Initialize model equality engine. This is called at the end of finish
   * init, after we have created a model object but before we have assigned it
   * an equality engine.
   */
  virtual void initializeModelEqEngine(eq::EqualityEngineNotify* notify) = 0;
  /**
   * Collect model Boolean variables.
   * This asserts the values of all boolean variables to the equality engine of
   * the model, based on their value in the prop engine.
   *
   * @return true if we are in conflict.
   */
  bool collectModelBooleanVariables();

  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** The equality engine manager */
  EqEngineManager& d_eem;
  /**
   * A dummy context for the model equality engine, so we can clear it
   * independently of search context.
   */
  context::Context d_modelEeContext;
  /** Pointer to the equality engine of the model */
  eq::EqualityEngine* d_modelEqualityEngine;
  /** The equality engine of the model, if we allocated it */
  std::unique_ptr<eq::EqualityEngine> d_modelEqualityEngineAlloc;
  /** The model object we have allocated (if one exists) */
  std::unique_ptr<TheoryModel> d_model;
  /** The model builder object we are using */
  TheoryEngineModelBuilder* d_modelBuilder;
  /** The model builder object we have allocated (if one exists) */
  std::unique_ptr<TheoryEngineModelBuilder> d_alocModelBuilder;
  /** whether we have tried to build this model in the current context */
  bool d_modelBuilt;
  /** whether this model has been built successfully */
  bool d_modelBuiltSuccess;
};

}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__MODEL_MANAGER__H */
