/*********************                                                        */
/*! \file model_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Abstract management of models for TheoryEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__MODEL_MANAGER__H
#define CVC4__THEORY__MODEL_MANAGER__H

#include <memory>

#include "theory/ee_manager.h"
#include "theory/logic_info.h"
#include "theory/theory_model.h"
#include "theory/theory_model_builder.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * A base class for managing models. Its main feature is to implement a
 * buildModel command. Overall, its behavior is specific to the kind of equality
 * engine management mode we are using. In particular, the prepare model
 * method is a manager-specific way for setting up the equality engine of the
 * model in preparation for model building.
 */
class ModelManager
{
 public:
  ModelManager(TheoryEngine& te, EqEngineManager& eem);
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
  theory::TheoryModel* getModel();
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
  /**
   * Collect asserted terms for theory with the given identifier, add to
   * termSet.
   *
   * @param tid The theory whose assertions we are collecting
   * @param termSet The set to add terms to
   * @param includeShared Whether to include the shared terms of the theory
   */
  void collectAssertedTerms(TheoryId tid,
                            std::set<Node>& termSet,
                            bool includeShared = true) const;
  /**
   * Helper function for collectAssertedTerms, adds all subterms
   * belonging to theory tid to termSet.
   */
  void collectTerms(TheoryId tid, TNode n, std::set<Node>& termSet) const;
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
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
  /** The model object we are using */
  theory::TheoryModel* d_model;
  /** The model object we have allocated (if one exists) */
  std::unique_ptr<theory::TheoryModel> d_alocModel;
  /** The model builder object we are using */
  theory::TheoryEngineModelBuilder* d_modelBuilder;
  /** The model builder object we have allocated (if one exists) */
  std::unique_ptr<theory::TheoryEngineModelBuilder> d_alocModelBuilder;
  /** whether we have tried to build this model in the current context */
  bool d_modelBuilt;
  /** whether this model has been built successfully */
  bool d_modelBuiltSuccess;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__MODEL_MANAGER__H */
