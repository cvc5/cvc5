/*********************                                                        */
/*! \file model_manager_distributed.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for model generation.
 **/

#include "theory/model_manager_distributed.h"

#include "theory/theory_engine.h"
#include "theory/theory_model.h"

namespace CVC4 {
namespace theory {

ModelManagerDistributed::ModelManagerDistributed(TheoryEngine& te,
                                                 EqEngineManager& eem)
    : ModelManager(te, eem)
{
}

ModelManagerDistributed::~ModelManagerDistributed()
{
  // pop the model context which we pushed on initialization
  d_modelEeContext.pop();
}

void ModelManagerDistributed::initializeModelEqEngine(
    eq::EqualityEngineNotify* notify)
{
  // initialize the model equality engine, use the provided notification object,
  // which belongs e.g. to CombinationModelBased
  EeSetupInfo esim;
  esim.d_notify = notify;
  esim.d_name = d_model->getName() + "::ee";
  esim.d_constantsAreTriggers = false;
  d_modelEqualityEngineAlloc.reset(
      d_eem.allocateEqualityEngine(esim, &d_modelEeContext));
  d_modelEqualityEngine = d_modelEqualityEngineAlloc.get();
  // finish initializing the model
  d_model->finishInit(d_modelEqualityEngine);
  // We push a context during initialization since the model is cleared during
  // collectModelInfo using pop/push.
  d_modelEeContext.push();
}

bool ModelManagerDistributed::prepareModel()
{
  Trace("model-builder") << "ModelManagerDistributed: reset model..."
                         << std::endl;

  // push/pop to clear the equality engine of the model
  d_modelEeContext.pop();
  d_modelEeContext.push();

  // Collect model info from the theories
  Trace("model-builder") << "ModelManagerDistributed: Collect model info..."
                         << std::endl;
  // Consult each active theory to get all relevant information concerning the
  // model, which includes both dump their equality information and assigning
  // values. Notice the order of theories here is important and is the same
  // as the list in CVC4_FOR_EACH_THEORY in theory_engine.cpp.
  for (TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST;
       ++theoryId)
  {
    if (!d_logicInfo.isTheoryEnabled(theoryId))
    {
      // theory not active, skip
      continue;
    }
    Theory* t = d_te.theoryOf(theoryId);
    Trace("model-builder") << "  CollectModelInfo on theory: " << theoryId
                           << std::endl;
    if (!t->collectModelInfo(d_model))
    {
      Trace("model-builder")
          << "ModelManagerDistributed: fail collect model info" << std::endl;
      return false;
    }
  }

  if (!collectModelBooleanVariables())
  {
    Trace("model-builder") << "ModelManagerDistributed: fail Boolean variables"
                           << std::endl;
    return false;
  }

  return true;
}

bool ModelManagerDistributed::finishBuildModel() const
{
  // do not use relevant terms
  if (!d_modelBuilder->buildModel(d_model))
  {
    Trace("model-builder") << "ModelManager: fail build model" << std::endl;
    return false;
  }
  return true;
}

}  // namespace theory
}  // namespace CVC4
