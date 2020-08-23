/*********************                                                        */
/*! \file model_manager.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for equality engines over
 ** all theories.
 **/

#include "theory/model_manager.h"

#include "options/theory_options.h"
#include "theory/quantifiers_engine.h"
#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

ModelManager::ModelManager(TheoryEngine& te)
    : d_te(te),
      d_logicInfo(te.getLogicInfo()),
      d_model(nullptr),
      d_modelBuilder(nullptr),
      d_modelBuilt(false),
      d_modelBuiltSuccess(false)
{
}

ModelManager::~ModelManager() {}

void ModelManager::finishInit()
{
  // construct the model
  const LogicInfo& logicInfo = d_te.getLogicInfo();
  // Initialize the model and model builder.
  if (logicInfo.isQuantified())
  {
    QuantifiersEngine* qe = d_te.getQuantifiersEngine();
    Assert(qe != nullptr);
    d_modelBuilder = qe->getModelBuilder();
    d_model = qe->getModel();
  }
  else
  {
    context::Context* u = d_te.getUserContext();
    d_alocModel.reset(
        new TheoryModel(u, "DefaultModel", options::assignFunctionValues()));
    d_model = d_alocModel.get();
  }

  // make the default builder, e.g. in the case that the quantifiers engine does
  // not have a model builder
  if (d_modelBuilder == nullptr)
  {
    d_alocModelBuilder.reset(new TheoryEngineModelBuilder(&d_te));
    d_modelBuilder = d_alocModelBuilder.get();
  }
  // notice that the equality engine of the model has yet to be assigned.
}

void ModelManager::resetModel()
{
  d_modelBuilt = false;
  d_modelBuiltSuccess = false;
  // Reset basic information on the model object
  d_model->reset();
}

bool ModelManager::buildModel()
{
  if (d_modelBuilt)
  {
    // already computed
    return d_modelBuiltSuccess;
  }
  // reset the flags now
  d_modelBuilt = true;
  d_modelBuiltSuccess = false;

  // prepare the model, which is specific to the manager
  if (!prepareModel())
  {
    Trace("model-builder") << "ModelManager: fail prepare model" << std::endl;
    return false;
  }

  // now, finish building the model
  d_modelBuiltSuccess = finishBuildModel();
  return d_modelBuiltSuccess;
}

bool ModelManager::isModelBuilt() const { return d_modelBuilt; }

void ModelManager::postProcessModel(bool incomplete)
{
  if (!d_modelBuilt)
  {
    // model not built, nothing to do
    return;
  }
  Trace("model-builder") << "ModelManager: post-process model..." << std::endl;
  // model construction should always succeed unless lemmas were added
  AlwaysAssert(d_modelBuiltSuccess);
  if (!options::produceModels())
  {
    return;
  }
  // Do post-processing of model from the theories (used for THEORY_SEP
  // to construct heap model)
  for (TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST;
       ++theoryId)
  {
    Theory* t = d_te.theoryOf(theoryId);
    if (t == nullptr)
    {
      // theory not active, skip
      continue;
    }
    Trace("model-builder-debug")
        << "  PostProcessModel on theory: " << theoryId << std::endl;
    t->postProcessModel(d_model);
  }
  // also call the model builder's post-process model
  d_modelBuilder->postProcessModel(incomplete, d_model);
}

theory::TheoryModel* ModelManager::getModel() { return d_model; }

bool ModelManager::finishBuildModel() const
{
  if (!d_modelBuilder->buildModel(d_model))
  {
    Trace("model-builder") << "ModelManager: fail build model" << std::endl;
    return false;
  }
  return true;
}

bool ModelManager::collectModelBooleanVariables()
{
  Trace("model-builder") << "  CollectModelInfo boolean variables" << std::endl;
  // Get value of the Boolean variables
  prop::PropEngine* propEngine = d_te.getPropEngine();
  std::vector<TNode> boolVars;
  propEngine->getBooleanVariables(boolVars);
  std::vector<TNode>::iterator it, iend = boolVars.end();
  bool hasValue, value;
  for (it = boolVars.begin(); it != iend; ++it)
  {
    TNode var = *it;
    hasValue = propEngine->hasValue(var, value);
    // Should we assert that hasValue is true?
    if (!hasValue)
    {
      Trace("model-builder-assertions")
          << "    has no value : " << var << std::endl;
      value = false;
    }
    Trace("model-builder-assertions")
        << "(assert" << (value ? " " : " (not ") << var
        << (value ? ");" : "));") << std::endl;
    if (!d_model->assertPredicate(var, value))
    {
      return false;
    }
  }
  return true;
}

}  // namespace theory
}  // namespace CVC4
