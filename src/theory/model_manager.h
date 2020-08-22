/*********************                                                        */
/*! \file model_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Abstract management of models for TheoryEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__MODEL_MANAGER__H
#define CVC4__THEORY__MODEL_MANAGER__H

#include <map>
#include <memory>

#include "theory/theory_model.h"
#include "theory/theory_model_builder.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * A base class for managing models. Its main feature is to implement a
 * buildModel command, which can be specific e.g. to the kind of equality
 * engine management mode we are using.
 */
class ModelManager
{
 public:
  ModelManager(TheoryEngine& te);
  virtual ~ModelManager();
  /** Finish initializing this class. */
  void finishInit();
  /** Reset model, called during full effort check before the model is built */
  void resetModel();
  /** 
   * Build the model, which calls the manager-specific buildModelInternal if
   * we have yet to build the model on this round.
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
 protected:
  /** 
   * Collect model Boolean variables.
   * This asserts the values of all boolean variables to the equality engine of
   * the model, based on their value in the prop engine.
   * 
   * @return true if we are in conflict.
   */
  bool collectModelBooleanVariables();
  /**
   * Build model internal, which the manager-specific method for building
   * models. This should assert all relevant information about the model into
   * the equality engine of d_model.
   *
   * @return true if we are in conflict.
   */
  virtual bool buildModelInternal() = 0;
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
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
